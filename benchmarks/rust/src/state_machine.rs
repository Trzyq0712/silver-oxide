//! Benchmark input: **dominator depth × arm count**.
//!
//! Unannotated Rust. A C-like `State` and `Event` enum matched against each other,
//! so a nested `match` produces a grid of arms: many sibling cubes (each dying at
//! the join) sitting under a shared dominator cube. Also the shape where a match
//! arm itself branches, giving cube suffixes on top of the arm's own literal.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 state_machine.rs

#[derive(Clone, Copy)]
pub enum State {
    Idle,
    Arming,
    Active,
    Cooling,
    Faulted,
}

#[derive(Clone, Copy)]
pub enum Event {
    Start,
    Stop,
    Tick,
    Fault,
    Reset,
}

pub struct Machine {
    pub state: State,
    pub timer: i32,
    pub faults: i32,
    pub cycles: i32,
}

pub fn machine_new() -> Machine {
    Machine {
        state: State::Idle,
        timer: 0,
        faults: 0,
        cycles: 0,
    }
}

pub fn state_code(s: State) -> i32 {
    match s {
        State::Idle => 0,
        State::Arming => 1,
        State::Active => 2,
        State::Cooling => 3,
        State::Faulted => 4,
    }
}

pub fn event_code(e: Event) -> i32 {
    match e {
        Event::Start => 0,
        Event::Stop => 1,
        Event::Tick => 2,
        Event::Fault => 3,
        Event::Reset => 4,
    }
}

pub fn state_is_running(s: State) -> bool {
    match s {
        State::Idle => false,
        State::Arming => true,
        State::Active => true,
        State::Cooling => true,
        State::Faulted => false,
    }
}

/// The 5x5 grid: outer match on state, inner match on event.
pub fn next_state(s: State, e: Event) -> State {
    match s {
        State::Idle => match e {
            Event::Start => State::Arming,
            Event::Stop => State::Idle,
            Event::Tick => State::Idle,
            Event::Fault => State::Faulted,
            Event::Reset => State::Idle,
        },
        State::Arming => match e {
            Event::Start => State::Arming,
            Event::Stop => State::Cooling,
            Event::Tick => State::Active,
            Event::Fault => State::Faulted,
            Event::Reset => State::Idle,
        },
        State::Active => match e {
            Event::Start => State::Active,
            Event::Stop => State::Cooling,
            Event::Tick => State::Active,
            Event::Fault => State::Faulted,
            Event::Reset => State::Idle,
        },
        State::Cooling => match e {
            Event::Start => State::Arming,
            Event::Stop => State::Idle,
            Event::Tick => State::Idle,
            Event::Fault => State::Faulted,
            Event::Reset => State::Idle,
        },
        State::Faulted => match e {
            Event::Start => State::Faulted,
            Event::Stop => State::Faulted,
            Event::Tick => State::Faulted,
            Event::Fault => State::Faulted,
            Event::Reset => State::Idle,
        },
    }
}

/// Arms that branch on top of the arm literal — cube suffixes over the match cube.
pub fn timer_after(s: State, e: Event, timer: i32) -> i32 {
    match e {
        Event::Tick => {
            if state_is_running(s) {
                if timer < 100 {
                    timer + 1
                } else {
                    100
                }
            } else {
                0
            }
        }
        Event::Start => 0,
        Event::Stop => {
            if timer < 10 {
                0
            } else {
                timer - 10
            }
        }
        Event::Fault => -1,
        Event::Reset => 0,
    }
}

/// `&mut` receiver mutated inside nested match arms.
pub fn machine_step(m: &mut Machine, e: Event) {
    let before = m.state;
    m.state = next_state(before, e);
    m.timer = timer_after(before, e, m.timer);
    match e {
        Event::Fault => {
            m.faults = m.faults + 1;
        }
        Event::Reset => {
            m.faults = 0;
            m.cycles = 0;
        }
        Event::Tick => {
            if state_is_running(before) {
                m.cycles = m.cycles + 1;
            }
        }
        Event::Start => {}
        Event::Stop => {}
    }
}

/// Three steps threaded through the same `&mut`, so each block's obligations sit on
/// top of the previous step's heap.
pub fn machine_run3(m: &mut Machine, a: Event, b: Event, c: Event) {
    machine_step(m, a);
    machine_step(m, b);
    machine_step(m, c);
}

pub fn machine_health(m: &Machine) -> i32 {
    let base = state_code(m.state) * 10;
    let penalty = m.faults * 7;
    if base < penalty {
        0
    } else {
        base - penalty + m.cycles
    }
}

/// Match over a pair encoded as two codes, with arithmetic in each arm — the shape
/// that makes every arm's cube carry a distinct integer fact.
pub fn transition_cost(s: State, e: Event) -> i32 {
    let sc = state_code(s);
    let ec = event_code(e);
    match e {
        Event::Start => sc * 2 + 1,
        Event::Stop => {
            if sc == 2 {
                sc * 3
            } else {
                sc + ec
            }
        }
        Event::Tick => {
            if state_is_running(s) {
                1
            } else {
                0
            }
        }
        Event::Fault => 100 - sc,
        Event::Reset => {
            if sc == 4 {
                50
            } else {
                sc * ec
            }
        }
    }
}

pub fn machine_settle(m: &mut Machine) {
    machine_step(m, Event::Stop);
    if m.timer == 0 {
        machine_step(m, Event::Reset);
    } else {
        machine_step(m, Event::Tick);
    }
}
