import socket
import struct
import os
import sys
import time
import threading
import logging
import json
import math
from bisect import bisect_left
import urllib.request
import urllib.error
import webbrowser
import tkinter as tk
from tkinter import ttk

from flask import Flask, jsonify, render_template
from copy import deepcopy


class QualifyingTelemetry:
    def __init__(self):
        self.key = None
        self.cars = {}
        self.generation = 0
        self.mini_records = [None] * 15

    @staticmethod
    def trace_time(trace, distance):
        if not trace or distance < trace[0][0] or distance > trace[-1][0]:
            return None
        i = bisect_left(trace, (distance, -1))
        if i < len(trace) and trace[i][0] == distance:
            return trace[i][1]
        if not i or i == len(trace):
            return None
        a, b = trace[i-1], trace[i]
        if b[0] - a[0] > 150 or b[1] - a[1] > 2000:
            return None
        return a[1] + (b[1]-a[1]) * (distance-a[0]) / (b[0]-a[0])

    def mini_times(self, state):
        times = [self.trace_time(state['trace'], d) for d in state['bounds']]
        return [round(b-a) if a is not None and b is not None else None
                for a, b in zip(times, times[1:])]

    def start_trace(self, state):
        state['trace'] = []
        state['personal_ref'] = state.get('best')
        leader = next((s for s in self.cars.values() if s.get('position') == 1), None)
        state['leader_ref'] = leader.get('best') if leader else None

    def live_comparison(self, state, reference):
        result = dict(delta_ms=None, car_index=reference.get('car') if reference else None,
                      lap=reference.get('lap') if reference else None, reason=None)
        if state['invalid']:
            result['reason'] = 'invalid_lap'
        elif state['status'] != 1 or state.get('pit'):
            result['reason'] = 'not_flying'
        elif not reference:
            result['reason'] = 'no_reference'
        elif not reference.get('trace'):
            result['reason'] = 'incomplete_reference'
        else:
            baseline = self.trace_time(reference.get('trace'), state.get('distance', -1))
            if baseline is not None:
                result['delta_ms'] = round(state['elapsed'] - baseline)
            else:
                result['reason'] = 'missing_distance_sample'
        return result

    def observe(self, key, car, lap, elapsed, last, sectors, invalid, status, pit, tyres, *, return_snapshot=True,
                distance=None, track_length=None, sector_starts=None, position=None, current_sector=None):
        if key != self.key:
            self.key = key
            self.cars = {}
            self.generation += 1
            self.mini_records = [None] * 15
        state = self.cars.get(car)
        new_run = bool(state and status == 1 and state['status'] in (0, 2, 3))
        if state and (lap < state['lap'] or (lap == state['lap'] and status == 1 and state['status'] == 1
                and elapsed + 2000 < state['elapsed'])):
            # Flashback/restart: previously recorded results are no longer reliable.
            self.cars = {}
            self.generation += 1
            self.mini_records = [None] * 15
            state = None
        if state is None:
            state = dict(lap=lap, elapsed=elapsed, sectors=[None]*3, invalid=bool(invalid),
                         status=status, history=[], tyres_start=None, set_condition='UNKNOWN')
            self.cars[car] = state
            state.update(best=None, position=position, bounds=[], distance=-1, pit=pit)
            self.start_trace(state)
        elif new_run and lap == state['lap']:
            # Leaving the garage/out-lap may restart the timed attempt without
            # changing m_currentLapNum. Keep completed results, refresh this run.
            state.update(sectors=[None]*3, invalid=False, tyres_start=deepcopy(tyres) if tyres else None)
            self.start_trace(state)

        # If the tracker joined after the out-lap had already started, there
        # may be no lap-number transition to attach the tyre snapshot to.
        # Capture the first trustworthy on-track reading as the start state.
        if (state['tyres_start'] is None and tyres and not pit
                and status in (1, 4)):
            state['tyres_start'] = deepcopy(tyres)
        if lap != state['lap']:
            if lap == state['lap'] + 1 and last > 0:
                split = state['sectors'][:]
                if split[0] and split[1] and last > split[0] + split[1]:
                    split[2] = last - split[0] - split[1]
                valid = not state['invalid'] and state['status'] == 1
                trace = state['trace']
                if trace and state['bounds'] and trace[-1][0] < state['bounds'][-1]:
                    trace.append((state['bounds'][-1], last))
                minis = self.mini_times(state)
                state['history'].append(dict(lap=state['lap'], time_ms=last, valid=valid,
                    sectors=split, tyres_start=state['tyres_start'], set_condition=state['set_condition'], mini_times=minis))
                if valid:
                    for j, value in enumerate(minis):
                        if value is not None and (self.mini_records[j] is None or value < self.mini_records[j]):
                            self.mini_records[j] = value
                    if state['best'] is None or last < state['best']['time_ms']:
                        # Preserve recorded portions of the actual best lap.
                        # trace_time rejects each missing interval individually;
                        # one gap must not disable comparisons elsewhere.
                        state['best'] = dict(car=car, lap=state['lap'], time_ms=last,
                                             trace=trace[:], mini_times=minis)
                state['history'] = state['history'][-100:]
            state.update(lap=lap, sectors=[None]*3, invalid=False,
                         tyres_start=deepcopy(tyres) if not pit else None)
            self.start_trace(state)
        # Observe the fitted set in the garage, before the out lap uses any rubber.
        if pit == 2 or status == 0:
            wear = tyres.get('wear') if tyres else None
            if wear and all(v is not None for v in wear.values()):
                state['set_condition'] = ('NEW' if tyres.get('age') == 0 and
                    all(v == 0 for v in wear.values()) else 'USED')
            else:
                state['set_condition'] = 'UNKNOWN'
        for i, value in enumerate(sectors[:2]):
            if current_sector is not None and current_sector <= i:
                state['sectors'][i] = None
            elif value and value > 0:
                state['sectors'][i] = value
        if current_sector is not None:
            state['sectors'][2] = None
        state.update(elapsed=elapsed, invalid=state['invalid'] or bool(invalid), status=status)
        state.update(position=position, pit=pit)
        if track_length and math.isfinite(track_length) and track_length > 0:
            starts = sector_starts or ()
            edges = [0, *starts, track_length] if len(starts) == 2 and 0 < starts[0] < starts[1] < track_length else [0, track_length/3, track_length*2/3, track_length]
            bounds = [edges[s] + (edges[s+1]-edges[s])*i/5 for s in range(3) for i in range(5)] + [track_length]
            if state['bounds'] and state['bounds'] != bounds:
                state['trace'] = []
            state['bounds'] = bounds
            if distance is not None and math.isfinite(distance) and 0 <= distance <= track_length:
                state['distance'] = distance
                trace = state['trace']
                if status == 1 and not pit and not state['invalid']:
                    if not trace and distance <= 50 and elapsed <= 1000:
                        trace.append((0, 0))
                    if not trace or (distance > trace[-1][0] and elapsed >= trace[-1][1] and distance-trace[-1][0] >= 10):
                        trace.append((distance, elapsed))
            else:
                state['distance'] = -1
        # A driver can leave the garage before the current leader has
        # completed a first timed lap.  In that case the reference is not
        # known when start_trace() runs.  Attach it as soon as it becomes
        # available during the same flying attempt instead of leaving the
        # leader delta unavailable for the whole lap.
        if status == 1 and not pit and not state['invalid'] and state.get('leader_ref') is None:
            leader = next((s for s in self.cars.values() if s.get('position') == 1), None)
            leader_best = leader.get('best') if leader else None
            if leader_best:
                state['leader_ref'] = deepcopy(leader_best)
        return self.snapshot(car) if return_snapshot else None

    def snapshot(self, car):
        state = self.cars.get(car)
        if state is None:
            return None
        return deepcopy(dict(lap=state['lap'], sectors=state['sectors'], invalid=state['invalid'],
            driver_status=state['status'], history=state['history'], tyres_start=state['tyres_start'],
            set_condition=state['set_condition'], generation=self.generation,
            mini_times=self.mini_times(state), mini_personal=state['personal_ref'].get('mini_times', []) if state['personal_ref'] else [],
            mini_records=self.mini_records, live_delta=dict(
                personal=self.live_comparison(state, state['personal_ref']),
                leader=self.live_comparison(state, state['leader_ref']))))

qualifying_telemetry = QualifyingTelemetry()


# ============================================================
# CONFIG
# ============================================================

UDP_IP = "127.0.0.1"
UDP_PORT = 20777

FLASK_HOST = "0.0.0.0"
FLASK_PORT = 5000

# Po wdrożeniu relay'a na Render wklej tutaj jego adres,
# np. https://f1-live-relay.onrender.com
REMOTE_RELAY_URL = os.environ.get(
    "F1_RELAY_URL",
    "https://f1-live-relay.onrender.com"
).rstrip("/")

REMOTE_SHARE_INTERVAL = 0.25

HEADER_SIZE = 29
MAX_CARS = 24


# ============================================================
# FLASK
# ============================================================

def resource_path(
    relative_path
):

    # Przy zwykłym `py tracker.py` szukamy plików względem
    # folderu, w którym faktycznie leży tracker.py, a nie
    # względem aktualnego katalogu terminala.
    # _MEIPASS zostaje jako fallback dla buildów, które go używają.
    if hasattr(
        sys,
        "_MEIPASS"
    ):

        base_path = sys._MEIPASS

    else:

        base_path = os.path.dirname(
            os.path.abspath(
                __file__
            )
        )

    return os.path.join(
        base_path,
        relative_path
    )


app = Flask(
    __name__,
    template_folder=resource_path(
        "templates"
    )
)

# Podczas testów lokalnych Flask/Jinja ma od razu zauważać
# podmianę templates/index.html po restarcie strony.
app.config[
    "TEMPLATES_AUTO_RELOAD"
] = True

# Wycisz zwykłe logi HTTP typu:
# 127.0.0.1 - - [...] "GET /api/data HTTP/1.1" 200 -
# Błędy nadal będą widoczne.
werkzeug_log = logging.getLogger(
    "werkzeug"
)
werkzeug_log.setLevel(
    logging.ERROR
)


def get_local_ip():

    sock = socket.socket(
        socket.AF_INET,
        socket.SOCK_DGRAM
    )

    try:

        # Nie wysyłamy żadnych danych.
        # To tylko pozwala Windowsowi wskazać,
        # którego lokalnego adresu używa aktywna sieć.
        sock.connect(
            (
                "8.8.8.8",
                80
            )
        )

        return sock.getsockname()[0]

    except Exception:

        try:

            return socket.gethostbyname(
                socket.gethostname()
            )

        except Exception:

            return "127.0.0.1"

    finally:

        sock.close()


# ============================================================
# PACKET NAMES
# ============================================================

PACKET_NAMES = {
    0: "Motion",
    1: "Session",
    2: "Lap Data",
    3: "Event",
    4: "Participants",
    5: "Car Setups",
    6: "Car Telemetry",
    7: "Car Status",
    8: "Final Classification",
    9: "Lobby Info",
    10: "Car Damage",
    12: "Tyre Sets",
    13: "Motion Ex",
    14: "Time Trial",
    15: "Lap Positions",
    16: "Car Telemetry 2",
}


TRACK_NAMES = {
    0: "Melbourne",
    2: "Shanghai",
    3: "Bahrain",
    4: "Catalunya",
    5: "Monaco",
    6: "Montreal",
    7: "Silverstone",
    9: "Hungaroring",
    10: "Spa",
    11: "Monza",
    12: "Singapore",
    13: "Suzuka",
    14: "Abu Dhabi",
    15: "Texas",
    16: "Brazil",
    17: "Austria",
    19: "Mexico",
    20: "Baku",
    26: "Zandvoort",
    27: "Imola",
    29: "Jeddah",
    30: "Miami",
    31: "Las Vegas",
    32: "Losail",
    39: "Silverstone Reverse",
    40: "Austria Reverse",
    41: "Zandvoort Reverse",
    42: "Madrid",
}


WEATHER_NAMES = {
    0: "CLEAR",
    1: "LIGHT CLOUD",
    2: "OVERCAST",
    3: "LIGHT RAIN",
    4: "HEAVY RAIN",
    5: "STORM",
}


SESSION_TYPE_NAMES = {
    0: "UNKNOWN",
    1: "PRACTICE 1",
    2: "PRACTICE 2",
    3: "PRACTICE 3",
    4: "SHORT PRACTICE",
    5: "QUALIFYING 1",
    6: "QUALIFYING 2",
    7: "QUALIFYING 3",
    8: "SHORT QUALIFYING",
    9: "ONE-SHOT QUALIFYING",
    10: "SPRINT SHOOTOUT 1",
    11: "SPRINT SHOOTOUT 2",
    12: "SPRINT SHOOTOUT 3",
    13: "SHORT SPRINT SHOOTOUT",
    14: "ONE-SHOT SPRINT SHOOTOUT",
    15: "RACE",
    16: "RACE 2",
    17: "RACE 3",
    18: "TIME TRIAL",
}


# ============================================================
# DATA
# ============================================================

drivers = {}
laps = {}
damage = {}
tyre_sets = {}
telemetry = {}
car_status = {}
motion = {}

# Historia ukończonych okrążeń budowana z Packet 2 (Lap Data).
lap_history = {}

# Snapshoty baterii na początku sektorów aktualnego okrążenia.
# Wartość zapisujemy dopiero po wykryciu przejścia do nowego sektora,
# używając pierwszego kolejnego Packet 7 (Car Status).
ers_sector_snapshots = {}

# Historia stintów opon.
# Dla każdego auta trzymamy zakończone stinty oraz aktualny komplet.
tyre_stints = {}

# Aktywne kary śledzone z Event Packet + Lap Data.
penalty_states = {}

# Ochrona przed przypadkowym podwójnym policzeniem tego samego eventu.
penalty_event_signatures = set()

# Do czyszczenia historii po zmianie sesji.
current_session_uid = None
publisher_car_index = None

# Dane ogólne sesji, np. łączna liczba okrążeń.
session_info = {}

# Stan komunikatów Race Control.
race_control = {
    "message": "",
    "type": "",
    "expires_at": 0.0,
}


remote_share = {
    "session_id": None,
    "publish_key": None,
    "view_url": None,
    "last_error": None,
    "last_publish_time": 0.0,
}

runtime_status = {
    "last_udp_time": 0.0,
    "udp_error": None,
}


# ============================================================
# HELPERS
# ============================================================

def parse_header(data):

    if len(data) < HEADER_SIZE:
        return None

    return {
        "format": struct.unpack_from("<H", data, 0)[0],
        "game_year": data[2],
        "major": data[3],
        "minor": data[4],
        "packet_version": data[5],
        "packet_id": data[6],
        "session_uid": struct.unpack_from("<Q", data, 7)[0],
        "session_time": struct.unpack_from("<f", data, 15)[0],
        "frame": struct.unpack_from("<I", data, 19)[0],
        "overall_frame": struct.unpack_from("<I", data, 23)[0],
        "player_car": data[27],
        "secondary_player": data[28],
    }


def ms_to_time(ms):

    if not ms or ms <= 0:
        return "--:--.---"

    minutes = ms // 60000
    seconds = (ms % 60000) / 1000

    return f"{minutes}:{seconds:06.3f}"


def delta_to_seconds(ms_part, minutes_part):

    return (
        minutes_part * 60000 + ms_part
    ) / 1000.0


def format_gap(seconds):

    if seconds is None:
        return "--"

    if seconds < 0:
        return f"-{abs(seconds):.3f}"

    return f"+{seconds:.3f}"



def get_penalty_state(
    car_idx
):

    if car_idx not in penalty_states:

        penalty_states[
            car_idx
        ] = {
            "time_penalties": [],
            "drive_throughs": [],
            "stop_go": [],
            "pit_serve_seen": False,
            "was_in_pit": False,
        }

    return penalty_states[
        car_idx
    ]


def penalty_event_seen(
    signature
):

    if signature in penalty_event_signatures:
        return True

    if len(
        penalty_event_signatures
    ) > 2000:

        penalty_event_signatures.clear()

    penalty_event_signatures.add(
        signature
    )

    return False


def register_penalty_event(
    penalty_type,
    infringement_type,
    vehicle_idx,
    other_vehicle_idx,
    penalty_time,
    lap_num,
    places_gained
):

    if (
        vehicle_idx < 0
        or vehicle_idx >= MAX_CARS
    ):
        return

    state = get_penalty_state(
        vehicle_idx
    )

    event = {
        "penalty_type":
            int(
                penalty_type
            ),
        "infringement_type":
            int(
                infringement_type
            ),
        "time":
            int(
                penalty_time
            ),
        "lap":
            int(
                lap_num
            ),
        "other_vehicle_idx":
            int(
                other_vehicle_idx
            ),
        "places_gained":
            int(
                places_gained
            ),
    }

    # 0 = Drive Through
    if penalty_type == 0:

        state[
            "drive_throughs"
        ].append(
            event
        )

        return

    # 1 = Stop Go
    if penalty_type == 1:

        state[
            "stop_go"
        ].append(
            event
        )

        return

    # 4 = Time Penalty
    if (
        penalty_type == 4
        and penalty_time > 0
    ):

        seconds = int(
            penalty_time
        )

        # 5 s / 10 s / kolejne wielokrotności 5 s mogą być
        # odsłużone w pit stopie. Np. +5 +3 = +8 total,
        # ale tylko 5 s jest servowalne.
        event[
            "servable_in_pit"
        ] = (
            seconds >= 5
            and seconds % 5 == 0
        )

        state[
            "time_penalties"
        ].append(
            event
        )


def mark_drive_through_served(
    vehicle_idx
):

    state = get_penalty_state(
        vehicle_idx
    )

    if state[
        "drive_throughs"
    ]:

        state[
            "drive_throughs"
        ].pop(
            0
        )


def mark_stop_go_served(
    vehicle_idx,
    stop_time
):

    state = get_penalty_state(
        vehicle_idx
    )

    active = state[
        "stop_go"
    ]

    if not active:
        return

    if (
        stop_time is None
        or stop_time <= 0
    ):

        active.pop(
            0
        )

        return

    best_index = 0
    best_delta = None

    for index, penalty in enumerate(
        active
    ):

        penalty_time = float(
            penalty.get(
                "time",
                0
            )
        )

        delta = abs(
            penalty_time
            - float(
                stop_time
            )
        )

        if (
            best_delta is None
            or delta < best_delta
        ):

            best_delta = delta
            best_index = index

    active.pop(
        best_index
    )


def serve_time_penalties_in_pit(
    vehicle_idx
):

    state = get_penalty_state(
        vehicle_idx
    )

    state[
        "time_penalties"
    ] = [
        penalty
        for penalty
        in state[
            "time_penalties"
        ]
        if not penalty.get(
            "servable_in_pit",
            False
        )
    ]


def update_penalty_pit_service(
    vehicle_idx,
    pit_status,
    pit_should_serve
):

    state = get_penalty_state(
        vehicle_idx
    )

    in_pit = pit_status in (
        1,
        2
    )

    if (
        in_pit
        and pit_should_serve
    ):

        state[
            "pit_serve_seen"
        ] = True

    was_in_pit = bool(
        state.get(
            "was_in_pit",
            False
        )
    )

    # Nie zdejmujemy czasu przy samym wjeździe.
    # Dopiero po opuszczeniu pit lane, jeśli gra zgłosiła
    # m_pitStopShouldServePen dla tego postoju.
    if (
        was_in_pit
        and not in_pit
    ):

        if state.get(
            "pit_serve_seen",
            False
        ):

            serve_time_penalties_in_pit(
                vehicle_idx
            )

        state[
            "pit_serve_seen"
        ] = False

    state[
        "was_in_pit"
    ] = in_pit


def get_penalty_summary(
    vehicle_idx,
    lap
):

    state = get_penalty_state(
        vehicle_idx
    )

    event_time_total = sum(
        max(
            0,
            int(
                penalty.get(
                    "time",
                    0
                )
            )
        )
        for penalty
        in state[
            "time_penalties"
        ]
    )

    lap_time_total = max(
        0,
        int(
            lap.get(
                "penalties",
                0
            )
        )
    )

    # Lap Data daje dobry fallback dla np. +3 s,
    # a Event Packet pozwala dołożyć 5/10 s.
    # max() zapobiega podwójnemu policzeniu tej samej +3 s.
    total_time = max(
        event_time_total,
        lap_time_total
    )

    servable_time = sum(
        max(
            0,
            int(
                penalty.get(
                    "time",
                    0
                )
            )
        )
        for penalty
        in state[
            "time_penalties"
        ]
        if penalty.get(
            "servable_in_pit",
            False
        )
    )

    servable_time = min(
        total_time,
        servable_time
    )

    # Bieżące liczniki DT / SG bierzemy z Lap Data.
    drive_through_count = max(
        0,
        int(
            lap.get(
                "num_unserved_drive_through",
                0
            )
        )
    )

    stop_go_count = max(
        0,
        int(
            lap.get(
                "num_unserved_stop_go",
                0
            )
        )
    )

    stop_go_times = [
        max(
            0,
            int(
                penalty.get(
                    "time",
                    0
                )
            )
        )
        for penalty
        in state[
            "stop_go"
        ][
            :stop_go_count
        ]
    ]

    return {
        "time_total":
            total_time,

        "servable_in_pit":
            servable_time,

        "drive_through_count":
            drive_through_count,

        "stop_go_count":
            stop_go_count,

        "stop_go_times":
            stop_go_times,

        "pit_should_serve":
            bool(
                lap.get(
                    "pit_stop_should_serve_pen",
                    0
                )
            ),
    }


def set_race_control(
    message,
    message_type,
    duration=None
):

    race_control["message"] = message
    race_control["type"] = message_type

    if duration is None:

        race_control["expires_at"] = 0.0

    else:

        race_control["expires_at"] = (
            time.monotonic()
            + duration
        )


def mark_race_finished():

    session_info[
        "race_finished"
    ] = True

    set_race_control(
        "RACE FINISHED",
        "finish"
    )


def clear_race_control():

    race_control["message"] = ""
    race_control["type"] = ""
    race_control["expires_at"] = 0.0


def get_race_control_state():

    expires_at = race_control.get(
        "expires_at",
        0.0
    )

    if (
        expires_at > 0
        and time.monotonic() >= expires_at
    ):

        clear_race_control()

    message = race_control.get(
        "message",
        ""
    )

    message_type = race_control.get(
        "type",
        ""
    )

    # Fallback: jeśli tracker został uruchomiony już w trakcie SC/VSC,
    # Packet 1 nadal pozwala pokazać aktywny stan.
    if not message:

        safety_status = session_info.get(
            "safety_car_status",
            0
        )

        if safety_status == 1:

            message = "SAFETY CAR"
            message_type = "sc"

        elif safety_status == 2:

            message = "VIRTUAL SAFETY CAR"
            message_type = "vsc"

    if not message:

        yellow_message = get_yellow_flag_message()

        if yellow_message:

            message = yellow_message
            message_type = "yellow"

    return {
        "message": message,
        "type": message_type,
    }


def get_yellow_flag_message():

    yellow_zones = [
        zone
        for zone
        in session_info.get(
            "marshal_zones",
            []
        )
        if int(
            zone.get(
                "flag",
                -1
            )
        ) == 3
    ]

    if not yellow_zones:
        return None

    track_length = float(
        session_info.get(
            "track_length",
            0
        )
        or 0
    )

    sector2_start = float(
        session_info.get(
            "sector2_lap_distance_start",
            0
        )
        or 0
    )

    sector3_start = float(
        session_info.get(
            "sector3_lap_distance_start",
            0
        )
        or 0
    )

    sectors = set()

    if (
        track_length > 0
        and sector2_start > 0
        and sector3_start > sector2_start
    ):

        for zone in yellow_zones:

            zone_start = float(
                zone.get(
                    "start",
                    -1
                )
            )

            if not 0 <= zone_start <= 1:
                continue

            distance = zone_start * track_length

            if distance < sector2_start:
                sectors.add(1)

            elif distance < sector3_start:
                sectors.add(2)

            else:
                sectors.add(3)

    if not sectors:
        return "YELLOW FLAG"

    if len(sectors) == 1:
        sector_text = f"SECTOR {next(iter(sectors))}"

    else:
        sector_text = "SECTORS " + ", ".join(
            str(sector)
            for sector
            in sorted(sectors)
        )

    return f"YELLOW FLAG — {sector_text}"


def tyre_compound_name(value):

    compounds = {
        16: "SOFT",
        17: "MEDIUM",
        18: "HARD",
        7: "INTER",
        8: "WET",
    }

    return compounds.get(
        value,
        "UNKNOWN"
    )


def update_tyre_stint(
    car_idx,
    visual_compound,
    tyres_age_laps
):

    compound = tyre_compound_name(
        visual_compound
    )

    if compound == "UNKNOWN":
        return

    try:

        age = int(
            tyres_age_laps
        )

    except (
        TypeError,
        ValueError
    ):

        return

    # 255 oznacza brak / nieważną wartość w wielu polach UDP.
    if age < 0 or age >= 250:
        return

    state = tyre_stints.get(
        car_idx
    )

    if state is None:

        tyre_stints[
            car_idx
        ] = {
            "completed": [],
            "current_compound":
                compound,
            "current_age":
                age,
            "max_age":
                age,
        }

        return

    current_compound = state.get(
        "current_compound",
        compound
    )

    current_age = int(
        state.get(
            "current_age",
            age
        )
    )

    max_age = int(
        state.get(
            "max_age",
            current_age
        )
    )

    # Nowy stint rozpoznajemy po zmianie mieszanki
    # albo po spadku wieku opony (np. 10L -> 0L/1L).
    new_stint = (
        compound != current_compound
        or age < current_age
    )

    if new_stint:

        completed = list(
            state.get(
                "completed",
                []
            )
        )

        completed.append({
            "compound":
                current_compound,
            "laps":
                max(
                    0,
                    max_age
                ),
        })

        # Wystarczający zapas nawet dla bardzo nietypowej strategii.
        completed = completed[
            -20:
        ]

        tyre_stints[
            car_idx
        ] = {
            "completed":
                completed,
            "current_compound":
                compound,
            "current_age":
                age,
            "max_age":
                age,
        }

        return

    state[
        "current_age"
    ] = age

    state[
        "max_age"
    ] = max(
        max_age,
        age
    )


def get_tyre_stint_history(
    car_idx
):

    state = tyre_stints.get(
        car_idx
    )

    if not state:
        return []

    history = [
        {
            "compound":
                stint.get(
                    "compound",
                    "UNKNOWN"
                ),
            "laps":
                int(
                    stint.get(
                        "laps",
                        0
                    )
                ),
            "current":
                False,
        }
        for stint
        in state.get(
            "completed",
            []
        )
    ]

    history.append({
        "compound":
            state.get(
                "current_compound",
                "UNKNOWN"
            ),
        "laps":
            int(
                state.get(
                    "current_age",
                    0
                )
            ),
        "current":
            True,
    })

    return history


def note_ers_sector_transition(
    car_idx,
    current_lap,
    sector
):

    if sector not in (
        0,
        1,
        2
    ):
        return

    state = ers_sector_snapshots.get(
        car_idx
    )

    # Przy pierwszym pakiecie nie znamy dokładnego momentu początku
    # bieżącego sektora, więc nie zapisujemy sztucznej wartości.
    # Dzięki temu po uruchomieniu trackera w połowie kółka widzimy "--"
    # aż do faktycznego przekroczenia następnej granicy sektora.
    if state is None:

        ers_sector_snapshots[
            car_idx
        ] = {
            "lap": int(
                current_lap
            ),
            "sector": int(
                sector
            ),
            "pending_sector": None,
            "values": [
                None,
                None,
                None,
            ],
        }

        return

    previous_lap = int(
        state.get(
            "lap",
            current_lap
        )
    )

    previous_sector = int(
        state.get(
            "sector",
            sector
        )
    )

    lap_changed = (
        int(current_lap)
        != previous_lap
    )

    sector_changed = (
        int(sector)
        != previous_sector
    )

    if lap_changed:

        state[
            "lap"
        ] = int(
            current_lap
        )

        state[
            "sector"
        ] = int(
            sector
        )

        state[
            "values"
        ] = [
            None,
            None,
            None,
        ]

        # Nowe okrążenie oznacza wejście do S1 (normalnie sector == 0).
        # Jeśli gra zwróci inny sektor, zapisujemy ten, który faktycznie podała.
        state[
            "pending_sector"
        ] = int(
            sector
        )

        return

    if sector_changed:

        state[
            "sector"
        ] = int(
            sector
        )

        state[
            "pending_sector"
        ] = int(
            sector
        )


def capture_pending_ers_sector(
    car_idx,
    ers_store_energy
):

    state = ers_sector_snapshots.get(
        car_idx
    )

    if not state:
        return

    pending_sector = state.get(
        "pending_sector"
    )

    if pending_sector not in (
        0,
        1,
        2
    ):
        return

    try:

        energy = float(
            ers_store_energy
        )

    except (
        TypeError,
        ValueError
    ):

        return

    if energy < 0:
        energy = 0.0

    percent = max(
        0.0,
        min(
            100.0,
            (
                energy
                / 4000000.0
            )
            * 100.0
        )
    )

    values = state.setdefault(
        "values",
        [
            None,
            None,
            None,
        ]
    )

    values[
        pending_sector
    ] = round(
        percent,
        1
    )

    state[
        "pending_sector"
    ] = None


def get_ers_sector_snapshot(
    car_idx
):

    state = ers_sector_snapshots.get(
        car_idx
    )

    if not state:

        return {
            "lap": 0,
            "S1": None,
            "S2": None,
            "S3": None,
        }

    values = list(
        state.get(
            "values",
            [
                None,
                None,
                None,
            ]
        )
    )

    while len(values) < 3:
        values.append(
            None
        )

    return {
        "lap": int(
            state.get(
                "lap",
                0
            )
        ),
        "S1": values[0],
        "S2": values[1],
        "S3": values[2],
    }


def remember_completed_lap(
    car_idx,
    current_lap,
    last_lap_time
):

    if last_lap_time <= 0:
        return

    # Jeśli aktualnie jedziemy np. LAP 2,
    # last_lap_time należy do ukończonego LAP 1.
    if current_lap <= 1:
        return

    completed_lap_number = (
        current_lap - 1
    )

    history_for_car = lap_history.setdefault(
        car_idx,
        []
    )

    # Packet 2 przychodzi wiele razy na sekundę,
    # więc aktualizujemy istniejący wpis zamiast duplikować.
    for entry in history_for_car:

        if entry["lap"] == completed_lap_number:

            entry["time_ms"] = last_lap_time
            entry["time"] = ms_to_time(
                last_lap_time
            )

            return

    history_for_car.append({

        "lap":
            completed_lap_number,

        "time_ms":
            last_lap_time,

        "time":
            ms_to_time(
                last_lap_time
            ),
    })

    history_for_car.sort(
        key=lambda entry: entry["lap"]
    )

    if len(history_for_car) > 100:
        del history_for_car[:-100]


# ============================================================
# PACKET 3 - EVENT / RACE CONTROL
# ============================================================

def parse_event(data):

    if len(data) < 33:
        return

    try:

        event_code = data[
            29:33
        ].decode(
            "ascii",
            errors="ignore"
        )

    except Exception:

        return

    # Chequered flag / race winner. The UDP stream can send either event,
    # depending on the session and the moment at which the listener joined.
    if (
        event_code in (
            "CHQF",
            "RCWN",
        )
        and int(
            session_info.get(
                "session_type",
                -1
            )
        ) in (
            15,
            16,
            17,
        )
    ):

        mark_race_finished()

        return

    # Penalty Issued.
    if (
        event_code == "PENA"
        and len(data) >= 40
    ):

        frame = struct.unpack_from(
            "<I",
            data,
            19
        )[0]

        penalty_type = data[33]
        infringement_type = data[34]
        vehicle_idx = data[35]
        other_vehicle_idx = data[36]
        penalty_time = data[37]
        lap_num = data[38]
        places_gained = data[39]

        signature = (
            frame,
            event_code,
            bytes(
                data[
                    33:40
                ]
            )
        )

        if not penalty_event_seen(
            signature
        ):

            register_penalty_event(
                penalty_type,
                infringement_type,
                vehicle_idx,
                other_vehicle_idx,
                penalty_time,
                lap_num,
                places_gained
            )

        return

    # Drive Through served.
    if (
        event_code == "DTSV"
        and len(data) >= 34
    ):

        vehicle_idx = data[33]

        mark_drive_through_served(
            vehicle_idx
        )

        return

    # Stop Go served.
    if (
        event_code == "SGSV"
        and len(data) >= 38
    ):

        vehicle_idx = data[33]

        stop_time = struct.unpack_from(
            "<f",
            data,
            34
        )[0]

        mark_stop_go_served(
            vehicle_idx,
            stop_time
        )

        return

    # Red flag shown.
    if event_code == "RDFL":

        set_race_control(
            "RED FLAG",
            "red"
        )

        return

    # Po czerwonej fladze gra nie zawsze wysyła ponownie SSTA.
    # Start lights / lights out są więc dodatkowym, dużo pewniejszym
    # sygnałem, że restart wyścigu już się rozpoczął.
    if event_code == "STLG":

        if race_control.get(
            "type"
        ) == "red":

            set_race_control(
                "RACE RESTART",
                "green",
                duration=3
            )

        return

    if event_code == "LGOT":

        # LGOT występuje również przy normalnym starcie, więc banner
        # pokazujemy tylko wtedy, gdy chwilę wcześniej aktywna była
        # czerwona flaga / restart po czerwonej fladze.
        if race_control.get(
            "type"
        ) in (
            "red",
            "green"
        ):

            set_race_control(
                "RACE RESUMED",
                "green",
                duration=4
            )

        return

    # Safety Car / Virtual Safety Car events.
    if (
        event_code == "SCAR"
        and len(data) >= 35
    ):

        safety_car_type = data[33]
        event_type = data[34]

        # Full Safety Car
        if safety_car_type == 1:

            if event_type == 0:

                set_race_control(
                    "SAFETY CAR",
                    "sc"
                )

            elif event_type == 1:

                set_race_control(
                    "SAFETY CAR IN THIS LAP",
                    "sc-ending"
                )

            elif event_type == 2:

                set_race_control(
                    "SAFETY CAR ENDED",
                    "green",
                    duration=4
                )

            elif event_type == 3:

                set_race_control(
                    "RACE RESUMED",
                    "green",
                    duration=4
                )

        # Virtual Safety Car
        elif safety_car_type == 2:

            if event_type == 0:

                set_race_control(
                    "VIRTUAL SAFETY CAR",
                    "vsc"
                )

            elif event_type == 1:

                set_race_control(
                    "VSC ENDING",
                    "vsc-ending"
                )

            elif event_type == 2:

                set_race_control(
                    "VSC ENDED",
                    "green",
                    duration=4
                )

            elif event_type == 3:

                set_race_control(
                    "RACE RESUMED",
                    "green",
                    duration=4
                )

        return

    # Po wznowieniu / starcie sesji zdejmujemy np. RED FLAG.
    if event_code == "SSTA":

        if race_control.get(
            "type"
        ) == "finish":

            clear_race_control()

        set_race_control(
            "RACE RESUMED",
            "green",
            duration=4
        )

        return

    # Koniec sesji - czyścimy banner.
    if event_code == "SEND":

        # Żółte strefy pochodzą z poprzedniego pakietu Session i nie mogą
        # zostać pokazane po zakończeniu sesji.
        session_info["marshal_zones"] = []

        if race_control.get(
            "type"
        ) != "finish":

            clear_race_control()


# ============================================================
# PACKET 4 - PARTICIPANTS
# ============================================================

def parse_participants(data):

    if len(data) < 30:
        return

    base = 30
    record_size = 60

    for i in range(MAX_CARS):

        offset = base + i * record_size

        if offset + record_size > len(data):
            break

        ai_controlled = data[offset]

        driver_id = struct.unpack_from(
            "<H", data, offset + 1
        )[0]

        network_id = struct.unpack_from(
            "<H", data, offset + 3
        )[0]

        team_id = struct.unpack_from(
            "<H", data, offset + 5
        )[0]

        my_team = data[offset + 7]
        race_number = data[offset + 8]
        nationality = data[offset + 9]

        name_raw = data[
            offset + 10:
            offset + 42
        ]

        try:

            name = name_raw.split(
                b"\x00", 1
            )[0].decode(
                "utf-8",
                errors="replace"
            )

        except Exception:

            name = "Unknown"

        your_telemetry = data[offset + 42]
        show_online_names = data[offset + 43]

        tech_level = struct.unpack_from(
            "<H",
            data,
            offset + 44
        )[0]

        platform = data[offset + 46]

        drivers[i] = {

            "name": name.strip() or f"Car {i}",

            "ai": ai_controlled,

            "driver_id": driver_id,

            "network_id": network_id,

            "team_id": team_id,

            "race_number": race_number,

            "telemetry_public":
                your_telemetry == 1,

            "online_name":
                show_online_names == 1,

            "platform": platform,
        }


# ============================================================
# PACKET 0 - MOTION
# ============================================================

def parse_motion(data):

    record_size = 54
    base = HEADER_SIZE

    for i in range(MAX_CARS):

        offset = (
            base
            + i * record_size
        )

        if (
            offset + record_size
            > len(data)
        ):
            break

        world_x = struct.unpack_from(
            "<f",
            data,
            offset
        )[0]

        world_y = struct.unpack_from(
            "<f",
            data,
            offset + 4
        )[0]

        world_z = struct.unpack_from(
            "<f",
            data,
            offset + 8
        )[0]

        yaw = struct.unpack_from(
            "<f",
            data,
            offset + 42
        )[0]

        motion[i] = {
            "world_x":
                world_x,

            "world_y":
                world_y,

            "world_z":
                world_z,

            "yaw":
                yaw,
        }


# ============================================================
# PACKET 1 - SESSION
# ============================================================

def parse_session(data):

    if len(data) <= 32:
        return

    # F1 25: 2026 Season Pack - PacketSessionData
    # Header ma 29 bajtów.
    weather = data[29]

    track_temperature = struct.unpack_from(
        "<b",
        data,
        30
    )[0]

    air_temperature = struct.unpack_from(
        "<b",
        data,
        31
    )[0]

    total_laps = data[32]

    session_info[
        "weather"
    ] = int(
        weather
    )

    session_info[
        "weather_name"
    ] = WEATHER_NAMES.get(
        weather,
        "UNKNOWN"
    )

    session_info[
        "track_temperature"
    ] = int(
        track_temperature
    )

    session_info[
        "air_temperature"
    ] = int(
        air_temperature
    )

    session_info[
        "total_laps"
    ] = total_laps

    # m_trackLength = offset 33, uint16 metres
    if len(data) > 34:

        session_info[
            "track_length"
        ] = struct.unpack_from(
            "<H",
            data,
            33
        )[0]

    # m_sessionType = offset 35
    if len(data) > 35:

        session_type = data[35]

        session_info[
            "session_type"
        ] = int(
            session_type
        )

        session_info[
            "session_type_name"
        ] = SESSION_TYPE_NAMES.get(
            session_type,
            f"SESSION {session_type}"
        )

    # m_trackId = offset 36, int8
    if len(data) > 36:

        track_id = struct.unpack_from(
            "<b",
            data,
            36
        )[0]

        session_info[
            "track_id"
        ] = track_id

        session_info[
            "track_name"
        ] = TRACK_NAMES.get(
            track_id,
            (
                f"Track {track_id}"
                if track_id >= 0
                else "Unknown Track"
            )
        )

    # m_sessionTimeLeft / m_sessionDuration
    if len(data) > 41:

        session_info[
            "session_time_left"
        ] = struct.unpack_from(
            "<H",
            data,
            38
        )[0]

        session_info[
            "session_duration"
        ] = struct.unpack_from(
            "<H",
            data,
            40
        )[0]

    # m_pitSpeedLimit = offset 42
    if len(data) > 42:

        session_info[
            "pit_speed_limit"
        ] = int(
            data[42]
        )

    # m_numMarshalZones = offset 47.
    # Każda MarshalZone ma 4 bajty początku strefy i 1 bajt flagi.
    marshal_zones = []

    if len(data) > 47:

        num_marshal_zones = min(
            int(
                data[47]
            ),
            21
        )

        for zone_index in range(
            num_marshal_zones
        ):

            offset = 48 + zone_index * 5

            if offset + 5 > len(data):
                break

            zone_start = struct.unpack_from(
                "<f",
                data,
                offset
            )[0]

            zone_flag = struct.unpack_from(
                "<b",
                data,
                offset + 4
            )[0]

            if 0 <= zone_start <= 1:

                marshal_zones.append({
                    "start": zone_start,
                    "flag": zone_flag,
                })

    session_info[
        "marshal_zones"
    ] = marshal_zones

    # Fixed 21 marshal zones end at offset 152.
    # m_safetyCarStatus = offset 153.
    if len(data) > 153:

        session_info[
            "safety_car_status"
        ] = int(
            data[153]
        )

    # m_sector2LapDistanceStart / m_sector3LapDistanceStart.
    # Te wartości pozwalają przypisać żółtą strefę do właściwego sektora.
    if len(data) > 748:

        session_info[
            "sector2_lap_distance_start"
        ] = struct.unpack_from(
            "<f",
            data,
            745
        )[0]

    if len(data) > 752:

        session_info[
            "sector3_lap_distance_start"
        ] = struct.unpack_from(
            "<f",
            data,
            749
        )[0]

    # m_numWeatherForecastSamples = offset 155.
    # Każdy WeatherForecastSample ma 8 bajtów:
    # sessionType, timeOffset, weather, trackTemperature,
    # trackTemperatureChange, airTemperature, airTemperatureChange,
    # rainPercentage.
    # Zachowujemy całą prognozę dla bieżącego typu sesji, żeby interfejs
    # mógł pokazać kolejne punkty deszczu na osi czasu.
    rain_percentage = None
    weather_forecast = []

    if len(data) > 155:

        num_samples = min(
            int(
                data[155]
            ),
            64
        )

        current_session_type = int(
            session_info.get(
                "session_type",
                0
            )
        )

        all_samples = []

        for sample_index in range(
            num_samples
        ):

            offset = (
                156
                + sample_index * 8
            )

            if offset + 8 > len(
                data
            ):
                break

            sample_session_type = int(
                data[offset]
            )

            time_offset = int(
                data[
                    offset + 1
                ]
            )

            sample_rain = int(
                data[
                    offset + 7
                ]
            )

            all_samples.append({
                "session_type": sample_session_type,
                "time_offset": time_offset,
                "weather": int(data[offset + 2]),
                "weather_name": WEATHER_NAMES.get(
                    int(data[offset + 2]),
                    "UNKNOWN"
                ),
                "track_temperature": struct.unpack_from(
                    "<b",
                    data,
                    offset + 3
                )[0],
                "track_temperature_change": struct.unpack_from(
                    "<b",
                    data,
                    offset + 4
                )[0],
                "air_temperature": struct.unpack_from(
                    "<b",
                    data,
                    offset + 5
                )[0],
                "air_temperature_change": struct.unpack_from(
                    "<b",
                    data,
                    offset + 6
                )[0],
                "rain_percentage": min(
                    100,
                    max(
                        0,
                        sample_rain
                    )
                ),
            })

        weather_forecast = [
            sample
            for sample in all_samples
            if sample["session_type"] == current_session_type
        ]

        if not weather_forecast:
            weather_forecast = all_samples

        weather_forecast.sort(
            key=lambda sample: sample["time_offset"]
        )

        if weather_forecast:
            rain_percentage = weather_forecast[0][
                "rain_percentage"
            ]

    session_info[
        "weather_forecast"
    ] = weather_forecast

    session_info[
        "rain_percentage"
    ] = rain_percentage


# ============================================================
# PACKET 2 - LAP DATA
# ============================================================

def parse_lap_data(data):

    global current_session_uid, publisher_car_index
    publisher_car_index = data[27] if data[27] < MAX_CARS else None

    session_uid = struct.unpack_from(
        "<Q",
        data,
        7
    )[0]

    if current_session_uid != session_uid:

        current_session_uid = session_uid
        lap_history.clear()
        ers_sector_snapshots.clear()
        tyre_stints.clear()
        penalty_states.clear()
        penalty_event_signatures.clear()
        motion.clear()

        session_info[
            "race_finished"
        ] = False

        if race_control.get(
            "type"
        ) == "finish":

            clear_race_control()

    record_size = 57
    base = 29

    for i in range(MAX_CARS):

        offset = base + i * record_size

        if offset + record_size > len(data):
            break

        last_lap = struct.unpack_from(
            "<I",
            data,
            offset
        )[0]

        current_lap_time = struct.unpack_from(
            "<I",
            data,
            offset + 4
        )[0]

        gap_front_ms = struct.unpack_from(
            "<H",
            data,
            offset + 14
        )[0]

        gap_front_min = data[offset + 16]

        gap_leader_ms = struct.unpack_from(
            "<H",
            data,
            offset + 17
        )[0]

        gap_leader_min = data[offset + 19]

        lap_distance = struct.unpack_from(
            "<f",
            data,
            offset + 20
        )[0]

        total_distance = struct.unpack_from(
            "<f",
            data,
            offset + 24
        )[0]

        position = data[offset + 32]

        current_lap = data[offset + 33]

        pit_status = data[offset + 34]

        num_pit_stops = data[offset + 35]

        sector = data[offset + 36]

        lap_invalid = data[offset + 37]

        penalties = data[offset + 38]

        total_warnings = data[
            offset + 39
        ]

        corner_cutting_warnings = data[
            offset + 40
        ]

        num_unserved_drive_through = data[
            offset + 41
        ]

        num_unserved_stop_go = data[
            offset + 42
        ]

        result_status = data[offset + 45]

        pit_stop_should_serve_pen = data[
            offset + 51
        ]

        note_ers_sector_transition(
            i,
            current_lap,
            sector
        )

        update_penalty_pit_service(
            i,
            pit_status,
            pit_stop_should_serve_pen
        )

        remember_completed_lap(
            i,
            current_lap,
            last_lap
        )

        session_type = session_info.get("session_type", 0)
        if 5 <= session_type <= 14:
            wear = damage.get(i, {}).get("tyres_wear")
            status_info = car_status.get(i, {})
            tyre_snapshot = {
                "compound": tyre_compound_name(status_info.get("visual_compound")),
                "age": status_info.get("tyres_age_laps"),
                "wear": dict(zip(("RL", "RR", "FL", "FR"), wear)) if wear else None,
            }
            # LapData: sector milliseconds + whole minutes; driver status follows grid position.
            sector1 = struct.unpack_from("<H", data, offset + 8)[0] + data[offset + 10] * 60000
            sector2 = struct.unpack_from("<H", data, offset + 11)[0] + data[offset + 13] * 60000
            qualifying_telemetry.observe(
                (str(session_uid), session_type, session_info.get("track_id")),
                i, current_lap, current_lap_time, last_lap,
                [sector1 if sector >= 1 else None, sector2 if sector >= 2 else None],
                lap_invalid, data[offset + 44], pit_status, tyre_snapshot,
                return_snapshot=False,
                distance=lap_distance, track_length=session_info.get('track_length'), position=position,
                current_sector=sector,
                sector_starts=(session_info.get('sector2_lap_distance_start', 0), session_info.get('sector3_lap_distance_start', 0)),
            )
        else:
            qualifying_telemetry.key = None
            qualifying_telemetry.cars.clear()

        laps[i] = {

            "last_lap": last_lap,

            "current_lap_time":
                current_lap_time,

            "gap_front":
                delta_to_seconds(
                    gap_front_ms,
                    gap_front_min
                ),

            "gap_leader":
                delta_to_seconds(
                    gap_leader_ms,
                    gap_leader_min
                ),

            "position": position,

            "current_lap": current_lap,

            "pit_status": pit_status,

            "num_pit_stops":
                num_pit_stops,

            "sector": sector,
            "driver_status": data[offset + 44],

            "invalid": lap_invalid,

            "penalties": penalties,

            "total_warnings":
                total_warnings,

            "corner_cutting_warnings":
                corner_cutting_warnings,

            "num_unserved_drive_through":
                num_unserved_drive_through,

            "num_unserved_stop_go":
                num_unserved_stop_go,

            "pit_stop_should_serve_pen":
                pit_stop_should_serve_pen,

            "result_status":
                result_status,

            "lap_distance":
                lap_distance,

            "total_distance":
                total_distance,
        }

    race_session = int(
        session_info.get(
            "session_type",
            -1
        )
    ) in (
        15,
        16,
        17,
    )

    if (
        race_session
        and not session_info.get(
            "race_finished",
            False
        )
    ):

        total_laps = int(
            session_info.get(
                "total_laps",
                0
            )
        )

        leader = next(
            (
                lap
                for lap in laps.values()
                if lap.get(
                    "position",
                    0
                ) == 1
            ),
            None
        )

        if (
            leader
            and total_laps > 0
            and int(
                leader.get(
                    "current_lap",
                    0
                )
            ) > total_laps
        ):

            mark_race_finished()


# ============================================================
# PACKET 6 - CAR TELEMETRY
# ============================================================

def parse_car_telemetry(data):

    record_size = 59
    base = 29

    for i in range(MAX_CARS):

        offset = base + i * record_size

        if offset + record_size > len(data):
            break

        # Wheel order in F1 UDP:
        # RL, RR, FL, FR

        tyre_surface_temp = list(
            data[
                offset + 30:
                offset + 34
            ]
        )

        tyre_inner_temp = list(
            data[
                offset + 34:
                offset + 38
            ]
        )

        telemetry[i] = {

            "tyre_surface_temp":
                tyre_surface_temp,

            "tyre_inner_temp":
                tyre_inner_temp,
        }


# ============================================================
# PACKET 7 - CAR STATUS
# ============================================================

def parse_car_status(data):

    record_size = 59
    base = 29

    for i in range(MAX_CARS):

        offset = base + i * record_size

        if offset + record_size > len(data):
            break

        actual_compound = data[
            offset + 25
        ]

        visual_compound = data[
            offset + 26
        ]

        tyres_age_laps = data[
            offset + 27
        ]

        ers_store_energy = struct.unpack_from(
            "<f",
            data,
            offset + 37
        )[0]

        ers_deploy_mode = data[
            offset + 41
        ]

        capture_pending_ers_sector(
            i,
            ers_store_energy
        )

        update_tyre_stint(
            i,
            visual_compound,
            tyres_age_laps
        )

        car_status[i] = {

            "actual_compound":
                actual_compound,

            "visual_compound":
                visual_compound,

            "tyres_age_laps":
                tyres_age_laps,

            "ers_store_energy":
                ers_store_energy,

            "ers_deploy_mode":
                ers_deploy_mode,
        }


# ============================================================
# PACKET 10 - DAMAGE
# ============================================================

def parse_damage(data):

    record_size = 46
    base = 29

    for i in range(MAX_CARS):

        offset = base + i * record_size

        if offset + record_size > len(data):
            break

        tyres_wear = struct.unpack_from(
            "<4f",
            data,
            offset
        )

        tyres_damage = list(
            data[
                offset + 16:
                offset + 20
            ]
        )

        brakes_damage = list(
            data[
                offset + 20:
                offset + 24
            ]
        )

        tyre_blisters = list(
            data[
                offset + 24:
                offset + 28
            ]
        )

        front_left_wing = data[
            offset + 28
        ]

        front_right_wing = data[
            offset + 29
        ]

        rear_wing = data[
            offset + 30
        ]

        floor = data[offset + 31]
        diffuser = data[offset + 32]
        sidepod = data[offset + 33]

        drs_fault = data[offset + 34]
        ers_fault = data[offset + 35]

        gearbox = data[offset + 36]
        engine = data[offset + 37]

        body_damage = [
            front_left_wing,
            front_right_wing,
            rear_wing,
            floor,
            diffuser,
            sidepod,
        ]

        damage[i] = {

            "tyres_wear":
                tyres_wear,

            "tyres_damage":
                tyres_damage,

            "brakes_damage":
                brakes_damage,

            "tyre_blisters":
                tyre_blisters,

            "front_left_wing":
                front_left_wing,

            "front_right_wing":
                front_right_wing,

            "rear_wing":
                rear_wing,

            "floor":
                floor,

            "diffuser":
                diffuser,

            "sidepod":
                sidepod,

            "gearbox":
                gearbox,

            "engine":
                engine,

            "drs_fault":
                drs_fault,

            "ers_fault":
                ers_fault,

            "body_max":
                max(
                    body_damage +
                    [
                        gearbox,
                        engine
                    ]
                ),
        }



# ============================================================
# PACKET 12 - TYRE SETS
# ============================================================

def parse_tyre_sets(data):

    if len(data) < 30:
        return

    car_idx = data[29]

    base = 30
    record_size = 10

    sets = []

    for i in range(20):

        offset = (
            base +
            i * record_size
        )

        if offset + record_size > len(data):
            break

        actual = data[offset]

        visual = data[
            offset + 1
        ]

        wear = data[
            offset + 2
        ]

        available = data[
            offset + 3
        ]

        recommended = data[
            offset + 4
        ]

        life_span = data[
            offset + 5
        ]

        usable_life = data[
            offset + 6
        ]

        lap_delta = struct.unpack_from(
            "<h",
            data,
            offset + 7
        )[0]

        fitted = data[
            offset + 9
        ]

        sets.append({

            "actual": actual,

            "visual": visual,

            "wear": wear,

            "available": available,

            "recommended":
                recommended,

            "life_span":
                life_span,

            "usable_life":
                usable_life,

            "lap_delta":
                lap_delta,

            "fitted":
                fitted,
        })

    fitted_idx = (
        data[230]
        if len(data) > 230
        else 255
    )

    tyre_sets[car_idx] = {

        "sets": sets,

        "fitted_idx":
            fitted_idx,
    }


# ============================================================
# WEB API
# ============================================================

@app.route("/")
def index():

    return render_template(
        "index.html"
    )


@app.route("/api/version")
def api_version():

    return jsonify({
        "version":
            "RACE-DASHBOARD-V26-SESSION-WEATHER",

        "lap_history_source":
            "Packet 2 - Lap Data",

        "best_lap_removed":
            True,
    })


@app.route("/api/data")
def api_data():


    output = []

    active = []

    for idx, lap in laps.items():

        if lap["position"] <= 0:
            continue

        active.append(
            (
                lap["position"],
                idx
            )
        )

    active.sort()
    
    for position, idx in active:

        driver = drivers.get(
            idx,
            {}
        )

        lap = laps.get(
            idx,
            {}
        )

        dmg = damage.get(
            idx,
            {}
        )


        telem = telemetry.get(
            idx,
            {}
        )

        status = car_status.get(
            idx,
            {}
        )

        motion_data = motion.get(
            idx,
            {}
        )

        tyres = dmg.get(
            "tyres_wear",
            [0, 0, 0, 0]
        )

        tyre_info = tyre_sets.get(
            idx,
            {}
        )

        fitted_idx = tyre_info.get(
            "fitted_idx",
            255
        )

        compound = tyre_compound_name(
            status.get(
                "visual_compound"
            )
        )

        sets = tyre_info.get(
            "sets",
            []
        )

        if (
            compound == "UNKNOWN"
            and fitted_idx != 255
            and 0 <= fitted_idx < len(sets)
        ):

            compound = tyre_compound_name(
                sets[fitted_idx].get(
                    "visual"
                )
            )

        output.append({

            "car_index":
                idx,

            "session_uid": str(current_session_uid),
            "publisher_name": drivers.get(publisher_car_index, {}).get("name"),
            "quali": qualifying_telemetry.snapshot(idx)
                if 5 <= session_info.get("session_type", 0) <= 14 else None,

            "position":
                position,

            "driver":
                driver.get(
                    "name",
                    f"Car {idx}"
                ),

            "team_id":
                driver.get(
                    "team_id",
                    65535
                ),

            "telemetry_public":
                driver.get(
                    "telemetry_public",
                    True
                ),

            "last_lap":
                ms_to_time(
                    lap.get(
                        "last_lap",
                        0
                    )
                ),

            "current_lap":
                lap.get(
                    "current_lap",
                    0
                ),

            "display_current_lap":
                (
                    lap.get(
                        "current_lap",
                        0
                    )
                    if lap.get(
                        "current_lap",
                        0
                    ) > 0
                    else (
                        lap_history.get(
                            idx,
                            []
                        )[-1]["lap"] + 1
                        if lap_history.get(
                            idx,
                            []
                        )
                        else 0
                    )
                ),

            "total_laps":
                session_info.get(
                    "total_laps",
                    0
                ),

            "track_length":
                session_info.get(
                    "track_length",
                    0
                ),

            "track_id":
                session_info.get(
                    "track_id",
                    -1
                ),

            "track_name":
                session_info.get(
                    "track_name",
                    "Unknown Track"
                ),

            "weather":
                session_info.get(
                    "weather",
                    0
                ),

            "weather_name":
                session_info.get(
                    "weather_name",
                    "UNKNOWN"
                ),

            "track_temperature":
                session_info.get(
                    "track_temperature"
                ),

            "air_temperature":
                session_info.get(
                    "air_temperature"
                ),

            "rain_percentage":
                session_info.get(
                    "rain_percentage"
                ),

            "weather_forecast":
                session_info.get(
                    "weather_forecast",
                    []
                ),

            "session_type":
                session_info.get(
                    "session_type",
                    0
                ),

            "session_type_name":
                session_info.get(
                    "session_type_name",
                    "UNKNOWN"
                ),

            "session_time_left":
                session_info.get(
                    "session_time_left",
                    0
                ),

            "session_duration":
                session_info.get(
                    "session_duration",
                    0
                ),

            "pit_speed_limit":
                session_info.get(
                    "pit_speed_limit",
                    0
                ),

            "world_x":
                round(
                    motion_data.get(
                        "world_x",
                        0.0
                    ),
                    2
                ),

            "world_z":
                round(
                    motion_data.get(
                        "world_z",
                        0.0
                    ),
                    2
                ),

            "yaw":
                round(
                    motion_data.get(
                        "yaw",
                        0.0
                    ),
                    4
                ),

            "lap_distance":
                round(
                    lap.get(
                        "lap_distance",
                        0.0
                    ),
                    1
                ),

            "total_distance":
                round(
                    lap.get(
                        "total_distance",
                        0.0
                    ),
                    1
                ),

            "lap_history":
                lap_history.get(
                    idx,
                    []
                ),

            "gap":
                format_gap(
                    lap.get(
                        "gap_front"
                    )
                ),

            "gap_leader":
                format_gap(
                    lap.get(
                        "gap_leader"
                    )
                ),

            "pit_status":
                lap.get(
                    "pit_status",
                    0
                ),

            "driver_status": lap.get("driver_status"),

            "penalty":
                get_penalty_summary(
                    idx,
                    lap
                ),

            "safety_car_status":
                session_info.get(
                    "safety_car_status",
                    0
                ),

            "race_control":
                get_race_control_state(),

            "compound":
                compound,

            "tyre_age_laps":
                status.get(
                    "tyres_age_laps",
                    0
                ),

            "tyre_stints":
                get_tyre_stint_history(
                    idx
                ),

            "ers_energy":
                round(
                    max(
                        0.0,
                        status.get(
                            "ers_store_energy",
                            0.0
                        )
                    ),
                    0
                ),

            "ers_percent":
                round(
                    max(
                        0.0,
                        min(
                            100.0,
                            (
                                status.get(
                                    "ers_store_energy",
                                    0.0
                                )
                                / 4000000.0
                            )
                            * 100.0
                        )
                    ),
                    1
                ),

            "ers_sectors":
                get_ers_sector_snapshot(
                    idx
                ),

            "ers_deploy_mode":
                status.get(
                    "ers_deploy_mode",
                    0
                ),

            "tyres": {

                "RL":
                    round(
                        tyres[0],
                        1
                    ),

                "RR":
                    round(
                        tyres[1],
                        1
                    ),

                "FL":
                    round(
                        tyres[2],
                        1
                    ),

                "FR":
                    round(
                        tyres[3],
                        1
                    ),
            },

            "tyre_temperatures": {

                "surface": {

                    "RL":
                        telem.get(
                            "tyre_surface_temp",
                            [0, 0, 0, 0]
                        )[0],

                    "RR":
                        telem.get(
                            "tyre_surface_temp",
                            [0, 0, 0, 0]
                        )[1],

                    "FL":
                        telem.get(
                            "tyre_surface_temp",
                            [0, 0, 0, 0]
                        )[2],

                    "FR":
                        telem.get(
                            "tyre_surface_temp",
                            [0, 0, 0, 0]
                        )[3],
                },

                "inner": {

                    "RL":
                        telem.get(
                            "tyre_inner_temp",
                            [0, 0, 0, 0]
                        )[0],

                    "RR":
                        telem.get(
                            "tyre_inner_temp",
                            [0, 0, 0, 0]
                        )[1],

                    "FL":
                        telem.get(
                            "tyre_inner_temp",
                            [0, 0, 0, 0]
                        )[2],

                    "FR":
                        telem.get(
                            "tyre_inner_temp",
                            [0, 0, 0, 0]
                        )[3],
                },
            },

            "front_wing": {

                "left":
                    dmg.get(
                        "front_left_wing",
                        0
                    ),

                "right":
                    dmg.get(
                        "front_right_wing",
                        0
                    ),
            },
        })

    return jsonify(output)



# ============================================================
# REMOTE SHARE
# ============================================================

def remote_share_enabled():

    url = REMOTE_RELAY_URL.strip()

    return (
        url.startswith("https://")
        and "PASTE-YOUR-RELAY" not in url
    )


def relay_request(
    method,
    path,
    payload=None,
    headers=None,
    timeout=10
):

    url = (
        REMOTE_RELAY_URL
        + path
    )

    body = None

    request_headers = {
        "User-Agent":
            "F1-26-Live-Timing/18",
    }

    if headers:

        request_headers.update(
            headers
        )

    if payload is not None:

        body = json.dumps(
            payload,
            separators=(
                ",",
                ":"
            )
        ).encode(
            "utf-8"
        )

        request_headers[
            "Content-Type"
        ] = "application/json"

    request = urllib.request.Request(
        url=url,
        data=body,
        headers=request_headers,
        method=method
    )

    with urllib.request.urlopen(
        request,
        timeout=timeout
    ) as response:

        raw = response.read()

        if not raw:
            return None

        return json.loads(
            raw.decode(
                "utf-8"
            )
        )


def clear_remote_session():

    remote_share["session_id"] = None
    remote_share["publish_key"] = None
    remote_share["view_url"] = None


def report_remote_error(message):

    if (
        remote_share.get(
            "last_error"
        ) != message
    ):

        print(
            f"[REMOTE] {message}"
        )

        remote_share[
            "last_error"
        ] = message


def report_remote_recovered():

    if remote_share.get(
        "last_error"
    ):

        print(
            "[REMOTE] Połączenie przywrócone."
        )

        remote_share[
            "last_error"
        ] = None

    remote_share[
        "last_publish_time"
    ] = time.monotonic()


def create_remote_session():

    data = relay_request(
        "POST",
        "/api/session/create",
        payload={
            "client":
                "F1 26 Live Timing",
            "version":
                "18"
        },
        timeout=90
    )

    if not data:

        raise RuntimeError(
            "Relay nie zwrócił danych sesji."
        )

    session_id = data.get(
        "session_id"
    )

    publish_key = data.get(
        "publish_key"
    )

    view_url = data.get(
        "view_url"
    )

    if not all(
        (
            session_id,
            publish_key,
            view_url
        )
    ):

        raise RuntimeError(
            "Niepełna odpowiedź relay'a."
        )

    remote_share[
        "session_id"
    ] = session_id

    remote_share[
        "publish_key"
    ] = publish_key

    remote_share[
        "view_url"
    ] = view_url

    remote_share[
        "last_error"
    ] = None

    print()
    print("=" * 60)
    print(" REMOTE SHARE: ACTIVE")
    print(
        f" SESSION CODE: "
        f"{session_id}"
    )
    print()
    print(" SEND THIS LINK TO YOUR ENGINEER:")
    print(
        f" {view_url}"
    )
    print()
    print(
        " Keep this window open while driving."
    )
    print("=" * 60)
    print()


def get_remote_snapshot():

    with app.app_context():

        response = api_data()

        return response.get_json()


def publish_remote_snapshot():

    session_id = remote_share.get(
        "session_id"
    )

    publish_key = remote_share.get(
        "publish_key"
    )

    if (
        not session_id
        or not publish_key
    ):

        create_remote_session()

        session_id = remote_share[
            "session_id"
        ]

        publish_key = remote_share[
            "publish_key"
        ]

    snapshot = get_remote_snapshot()

    relay_request(
        "POST",
        (
            f"/api/session/"
            f"{session_id}"
            f"/publish"
        ),
        payload={
            "data":
                snapshot,
            "sent_at":
                time.time()
        },
        headers={
            "X-Publish-Key":
                publish_key
        },
        timeout=8
    )


def remote_share_loop():

    time.sleep(
        1.5
    )

    if not remote_share_enabled():

        print(
            "[REMOTE] Udostępnianie wyłączone. "
            "Wklej adres relay'a do REMOTE_RELAY_URL."
        )

        return

    while True:

        try:

            publish_remote_snapshot()

            report_remote_recovered()

        except urllib.error.HTTPError as error:

            if error.code in (
                401,
                403,
                404,
                410
            ):

                clear_remote_session()

                report_remote_error(
                    (
                        f"Sesja relay'a wygasła "
                        f"({error.code}). "
                        "Tworzę nową..."
                    )
                )

            else:

                report_remote_error(
                    (
                        f"Relay HTTP "
                        f"{error.code}."
                    )
                )

        except urllib.error.URLError as error:

            report_remote_error(
                (
                    "Brak połączenia z relay'em: "
                    f"{error.reason}"
                )
            )

        except Exception as error:

            report_remote_error(
                (
                    "Błąd udostępniania: "
                    f"{error}"
                )
            )

        time.sleep(
            REMOTE_SHARE_INTERVAL
        )


# ============================================================
# UDP LISTENER
# ============================================================

def udp_listener():

    sock = socket.socket(
        socket.AF_INET,
        socket.SOCK_DGRAM
    )

    sock.setsockopt(
        socket.SOL_SOCKET,
        socket.SO_REUSEADDR,
        1
    )

    sock.bind(
        (
            UDP_IP,
            UDP_PORT
        )
    )

    sock.settimeout(0.05)

    print(
        f"Nasłuchiwanie F1 26 UDP "
        f"{UDP_IP}:{UDP_PORT}"
    )

    print(
        "Uruchom grę i wejdź na tor..."
    )

    while True:

        try:

            data, address = (
                sock.recvfrom(4096)
            )

            if len(data) < HEADER_SIZE:
                continue
            
            header = parse_header(
                data
            )

            if not header:
                continue


            if header["format"] != 2026:
                continue

            runtime_status[
                "last_udp_time"
            ] = time.monotonic()

            runtime_status[
                "udp_error"
            ] = None

            packet_id = header[
                "packet_id"
            ]

            try:

                if packet_id == 0:
                    parse_motion(data)

                elif packet_id == 1:
                    parse_session(data)

                elif packet_id == 2:
                    parse_lap_data(data)

                elif packet_id == 3:
                    parse_event(data)

                elif packet_id == 4:
                    parse_participants(data)

                elif packet_id == 6:
                    parse_car_telemetry(data)

                elif packet_id == 7:
                    parse_car_status(data)

                elif packet_id == 10:
                    parse_damage(data)


                elif packet_id == 12:
                    parse_tyre_sets(data)

            except Exception as e:

                print(
                    f"\nBłąd Packet "
                    f"{packet_id}: {e}"
                )

        except socket.timeout:

            pass

        except Exception as e:

            runtime_status[
                "udp_error"
            ] = str(e)

            print(
                f"\nBłąd UDP: {e}"
            )


# ============================================================
# GUI
# ============================================================

class LiveTimingGUI:

    def __init__(
        self,
        root
    ):

        self.root = root

        self.root.title(
            "F1 26 Live Timing"
        )

        self.root.geometry(
            "520x430"
        )

        self.root.minsize(
            500,
            410
        )

        self.root.configure(
            bg="#f4f4f4"
        )

        self.local_ip = (
            get_local_ip()
        )

        self.status_font = (
            "Segoe UI",
            10,
            "bold"
        )

        self.title_font = (
            "Segoe UI",
            18,
            "bold"
        )

        self.value_font = (
            "Consolas",
            10
        )

        self.build_ui()

        self.refresh_status()


    def build_ui(self):

        outer = tk.Frame(
            self.root,
            bg="#f4f4f4",
            padx=18,
            pady=16
        )

        outer.pack(
            fill="both",
            expand=True
        )

        tk.Label(
            outer,
            text="F1 26 LIVE TIMING",
            font=self.title_font,
            bg="#f4f4f4",
            fg="#111111"
        ).pack(
            anchor="w"
        )

        tk.Label(
            outer,
            text=(
                "Driver telemetry client"
            ),
            font=(
                "Segoe UI",
                9
            ),
            bg="#f4f4f4",
            fg="#666666"
        ).pack(
            anchor="w",
            pady=(
                0,
                14
            )
        )

        status_frame = tk.Frame(
            outer,
            bg="#ffffff",
            bd=1,
            relief="solid",
            padx=12,
            pady=10
        )

        status_frame.pack(
            fill="x"
        )

        self.telemetry_status = (
            self.make_status_row(
                status_frame,
                "Telemetry"
            )
        )

        self.remote_status = (
            self.make_status_row(
                status_frame,
                "Remote share"
            )
        )

        self.session_status = (
            self.make_status_row(
                status_frame,
                "Session"
            )
        )

        link_frame = tk.Frame(
            outer,
            bg="#f4f4f4"
        )

        link_frame.pack(
            fill="x",
            pady=(
                15,
                0
            )
        )

        tk.Label(
            link_frame,
            text="ENGINEER LINK",
            font=(
                "Segoe UI",
                9,
                "bold"
            ),
            bg="#f4f4f4",
            fg="#444444"
        ).pack(
            anchor="w"
        )

        self.link_text = tk.Text(
            link_frame,
            height=3,
            wrap="word",
            font=(
                "Consolas",
                9
            ),
            bg="#ffffff",
            fg="#222222",
            relief="solid",
            bd=1,
            padx=8,
            pady=7
        )

        self.link_text.pack(
            fill="x",
            pady=(
                5,
                8
            )
        )

        self.link_text.insert(
            "1.0",
            "Waiting for remote session..."
        )

        self.link_text.configure(
            state="disabled"
        )

        buttons = tk.Frame(
            link_frame,
            bg="#f4f4f4"
        )

        buttons.pack(
            fill="x"
        )

        self.copy_button = tk.Button(
            buttons,
            text="COPY ENGINEER LINK",
            command=self.copy_engineer_link,
            state="disabled",
            font=(
                "Segoe UI",
                9,
                "bold"
            ),
            padx=12,
            pady=7
        )

        self.copy_button.pack(
            side="left"
        )

        self.open_engineer_button = (
            tk.Button(
                buttons,
                text="OPEN LINK",
                command=self.open_engineer_link,
                state="disabled",
                font=(
                    "Segoe UI",
                    9
                ),
                padx=12,
                pady=7
            )
        )

        self.open_engineer_button.pack(
            side="left",
            padx=(
                8,
                0
            )
        )

        local_frame = tk.Frame(
            outer,
            bg="#f4f4f4"
        )

        local_frame.pack(
            fill="x",
            pady=(
                16,
                0
            )
        )

        tk.Label(
            local_frame,
            text="LOCAL VIEW",
            font=(
                "Segoe UI",
                9,
                "bold"
            ),
            bg="#f4f4f4",
            fg="#444444"
        ).pack(
            anchor="w"
        )

        self.local_label = tk.Label(
            local_frame,
            text=(
                f"http://127.0.0.1:"
                f"{FLASK_PORT}"
            ),
            font=self.value_font,
            bg="#f4f4f4",
            fg="#222222"
        )

        self.local_label.pack(
            anchor="w",
            pady=(
                4,
                0
            )
        )

        self.lan_label = tk.Label(
            local_frame,
            text=(
                f"http://{self.local_ip}:"
                f"{FLASK_PORT}"
            ),
            font=self.value_font,
            bg="#f4f4f4",
            fg="#555555"
        )

        self.lan_label.pack(
            anchor="w"
        )

        local_buttons = tk.Frame(
            local_frame,
            bg="#f4f4f4"
        )

        local_buttons.pack(
            anchor="w",
            pady=(
                7,
                0
            )
        )

        tk.Button(
            local_buttons,
            text="OPEN LOCAL VIEW",
            command=self.open_local_view,
            font=(
                "Segoe UI",
                9
            ),
            padx=10,
            pady=5
        ).pack(
            side="left"
        )

        footer = tk.Label(
            outer,
            text=(
                "Keep this window open while driving. "
                "Closing it stops telemetry sharing."
            ),
            font=(
                "Segoe UI",
                8
            ),
            bg="#f4f4f4",
            fg="#777777"
        )

        footer.pack(
            anchor="w",
            pady=(
                18,
                0
            )
        )


    def make_status_row(
        self,
        parent,
        label
    ):

        row = tk.Frame(
            parent,
            bg="#ffffff"
        )

        row.pack(
            fill="x",
            pady=3
        )

        tk.Label(
            row,
            text=label,
            width=15,
            anchor="w",
            font=(
                "Segoe UI",
                10
            ),
            bg="#ffffff",
            fg="#333333"
        ).pack(
            side="left"
        )

        value = tk.Label(
            row,
            text="WAITING",
            anchor="w",
            font=self.status_font,
            bg="#ffffff",
            fg="#a36b00"
        )

        value.pack(
            side="left"
        )

        return value


    def set_status(
        self,
        widget,
        text,
        color
    ):

        if (
            widget.cget(
                "text"
            ) != text
        ):

            widget.configure(
                text=text
            )

        if (
            widget.cget(
                "fg"
            ) != color
        ):

            widget.configure(
                fg=color
            )


    def set_link(
        self,
        value
    ):

        current = (
            self.link_text.get(
                "1.0",
                "end-1c"
            )
        )

        if current == value:
            return

        self.link_text.configure(
            state="normal"
        )

        self.link_text.delete(
            "1.0",
            "end"
        )

        self.link_text.insert(
            "1.0",
            value
        )

        self.link_text.configure(
            state="disabled"
        )


    def refresh_status(self):

        current = (
            time.monotonic()
        )

        udp_age = (
            current
            - runtime_status.get(
                "last_udp_time",
                0.0
            )
        )

        if (
            runtime_status.get(
                "udp_error"
            )
        ):

            self.set_status(
                self.telemetry_status,
                "ERROR",
                "#b00020"
            )

        elif (
            runtime_status.get(
                "last_udp_time",
                0.0
            ) > 0
            and udp_age < 2.0
        ):

            self.set_status(
                self.telemetry_status,
                "CONNECTED",
                "#16823b"
            )

        else:

            self.set_status(
                self.telemetry_status,
                "WAITING FOR F1 26",
                "#a36b00"
            )

        view_url = (
            remote_share.get(
                "view_url"
            )
        )

        session_id = (
            remote_share.get(
                "session_id"
            )
        )

        last_publish = (
            remote_share.get(
                "last_publish_time",
                0.0
            )
        )

        publish_age = (
            current
            - last_publish
        )

        remote_error = (
            remote_share.get(
                "last_error"
            )
        )

        if remote_error:

            self.set_status(
                self.remote_status,
                "RECONNECTING",
                "#b00020"
            )

        elif (
            view_url
            and last_publish > 0
            and publish_age < 3.0
        ):

            self.set_status(
                self.remote_status,
                "LIVE",
                "#16823b"
            )

        elif view_url:

            self.set_status(
                self.remote_status,
                "CONNECTING",
                "#a36b00"
            )

        else:

            self.set_status(
                self.remote_status,
                "CREATING SESSION",
                "#a36b00"
            )

        if session_id:

            self.set_status(
                self.session_status,
                session_id,
                "#111111"
            )

        else:

            self.set_status(
                self.session_status,
                "—",
                "#777777"
            )

        if view_url:

            self.set_link(
                view_url
            )

            if (
                str(
                    self.copy_button[
                        "state"
                    ]
                ) != "normal"
            ):

                self.copy_button.configure(
                    state="normal"
                )

                self.open_engineer_button.configure(
                    state="normal"
                )

        else:

            self.set_link(
                "Waiting for remote session..."
            )

        self.root.after(
            250,
            self.refresh_status
        )


    def copy_engineer_link(self):

        view_url = (
            remote_share.get(
                "view_url"
            )
        )

        if not view_url:
            return

        self.root.clipboard_clear()

        self.root.clipboard_append(
            view_url
        )

        self.root.update()

        original = (
            self.copy_button.cget(
                "text"
            )
        )

        self.copy_button.configure(
            text="COPIED!"
        )

        self.root.after(
            1200,
            lambda:
                self.copy_button.configure(
                    text=original
                )
        )


    def open_engineer_link(self):

        view_url = (
            remote_share.get(
                "view_url"
            )
        )

        if view_url:

            webbrowser.open(
                view_url
            )


    def open_local_view(self):

        webbrowser.open(
            (
                "http://127.0.0.1:"
                f"{FLASK_PORT}"
            )
        )


def run_flask_server():

    app.run(
        host=FLASK_HOST,
        port=FLASK_PORT,
        debug=False,
        threaded=True,
        use_reloader=False
    )


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    udp_thread = threading.Thread(
        target=udp_listener,
        daemon=True
    )

    udp_thread.start()

    remote_thread = threading.Thread(
        target=remote_share_loop,
        daemon=True
    )

    remote_thread.start()

    flask_thread = threading.Thread(
        target=run_flask_server,
        daemon=True
    )

    flask_thread.start()

    root = tk.Tk()

    gui = LiveTimingGUI(
        root
    )

    root.mainloop()

