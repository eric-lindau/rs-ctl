use std::collections::HashSet;
use std::collections::HashMap;

/// Existential Normal Form (ENF) formula atoms.
#[derive(Debug)]
enum Enf<'a> {
    True,
    Prop(String),
    // References required to compile a finite enum
    And(&'a Enf<'a>, &'a Enf<'a>),
    Not(&'a Enf<'a>),
    ExistsNext(&'a Enf<'a>),
    ExistsUntil(&'a Enf<'a>, &'a Enf<'a>),
    ExistsAlways(&'a Enf<'a>),
}

/// State type for a Transition System.
type State = i32;

/// Simplified Transition System abstraction.
struct TransitionSystem<'a> {
    // state set S
    states: &'a HashSet<State>,
    // initial states I, subset of S
    initial_states: &'a HashSet<State>,
    // transition relation T: S -> S (action set Act is excluded)
    transitions: &'a HashMap<State, HashSet<State>>,
    // transition backedge relation, inverse of T
    transitions_back: &'a HashMap<State, HashSet<State>>,
    // labeling relation L: S -> 2^(AP)
    label: &'a HashMap<State, HashSet<String>>,
}

impl<'a> TransitionSystem<'a> {
    pub fn new(
        states: &'a HashSet<State>,
        // initial states I, subset of S
        initial_states: &'a HashSet<State>,
        // transition relation T: S -> S (action set Act is excluded)
        transitions: &'a HashMap<State, HashSet<State>>,
        transitions_back: &'a HashMap<State, HashSet<State>>,
        // labeling relation L: S -> 2^(AP)
        label: &'a HashMap<State, HashSet<String>>,
    ) -> TransitionSystem<'a> {
        TransitionSystem {
            states,
            initial_states,
            transitions,
            transitions_back,
            label,
        }
    }

    pub fn sat(&self, e: &Enf) -> HashSet<State> {
        match e {
            // Sat(true) = S
            Enf::True => self.states.iter().copied().collect(),

            // Sat(a) = {s in S | a in L(s) for any a in AP}
            Enf::Prop(str) =>
                self.states_where(
                    |state|
                        self.label.get(state)
                            .unwrap()
                            .contains(str)
                ),

            // Sat(phi and psi) = Sat(phi) intersect Sat(psi)
            Enf::And(phi, psi) =>
                self.sat(phi)
                    .intersection(&self.sat(psi))
                    .copied()
                    .collect(),

            // Sat(~phi) = S \ Sat(phi)
            Enf::Not(phi) =>
                self.states
                    .difference(&self.sat(phi))
                    .copied()
                    .collect(),

            // Sat(next phi) = {s in S | Post(s) intersect Sat(phi) != empty}
            Enf::ExistsNext(phi) =>
                self.states_where(
                    |state|
                        !self.transitions.get(state)
                            .unwrap()
                            .intersection(
                                &self.sat(phi)
                            )
                            .collect::<Vec<&State>>()
                            .is_empty()
                ),

            // Sat(exists until phi) = min(T = {})
            Enf::ExistsUntil(phi, psi) => {
                let phi_sat: HashSet<State> = self.sat(phi);
                let psi_sat: HashSet<State> = self.sat(psi);

                let mut valid_states: HashSet<State> = HashSet::new();
                let mut visited: HashSet<State> = HashSet::new();
                for terminal_state in psi_sat.iter() {
                    valid_states.extend(
                        self.exists_until_dfs(
                            terminal_state,
                            &self.sat(phi),
                            &mut visited,
                        )
                    );
                }

                valid_states
            }

            // TODO
            // Sat(exists always phi) =
            Enf::ExistsAlways(phi) =>
                self.states
                    .iter()
                    .copied()
                    .collect()

            // TODO ***: add other atomics based on proven equivalences
        }
    }

    fn exists_until_dfs(&self, node: &State, phi_sat: &HashSet<State>, visited: &mut HashSet<State>) -> HashSet<State> {
        let mut valid_states: HashSet<State> = HashSet::new();

        let adjacent: &HashSet<State> = self.transitions_back.get(&node).unwrap();
        let adjacent: Vec<State> = adjacent.iter()
            .filter(|state| !visited.contains(*state))
            .copied()
            .collect::<Vec<State>>();

        for adjacent_node in adjacent.iter().copied() {
            visited.insert(adjacent_node);
            if phi_sat.contains(&adjacent_node) {
                valid_states.insert(adjacent_node);
                let valid_predecessors: HashSet<State> = self.exists_until_dfs(
                    &adjacent_node,
                    phi_sat,
                    visited,
                );
                valid_states.extend(valid_predecessors);
            }
        }

        valid_states
    }

    fn states_where<F: Fn(&State) -> bool>(&self, pred: F) -> HashSet<State> {
        self.states
            .iter()
            .copied()
            .filter(|state| pred(state))
            .collect()
    }
}


// Based on SOURCE: https://stackoverflow.com/questions/27582739/how-do-i-create-a-hashmap-literal
macro_rules! adjacency_map (
    { $($key:expr => {$($value:expr),+}),+ } => {
        {
            let mut m = ::std::collections::HashMap::new();
            $(
                let mut s = ::std::collections::HashSet::new();
                $(
                    s.insert($value);
                )+
                m.insert($key, s);
            )+
            m
        }
     };
);

macro_rules! set (
    { $($value:expr),+ } => {
        {
            let mut s = ::std::collections::HashSet::new();
            $(
                s.insert($value);
            )+
            s
        }
     };
);


#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use crate::{TransitionSystem, Enf};

    #[test]
    /// Simple TS found on page 325 of 'Principles of Model Checking'
    fn simple_ts() {
        let mut states = HashSet::new();
        states.insert(0);
        states.insert(1);
        states.insert(2);
        states.insert(3);
        let initial_states = states.iter().copied().collect();
        let transitions = adjacency_map! {0 => {1, 2}, 1 => {0, 3}, 2 => {1}, 3 => {3}};
        let transitions_back = adjacency_map! {0 => {1, 2}, 1 => {0, 2}, 2 => {0}, 3 => {1, 3}};
        let label = adjacency_map! {
            0 => {"a".into()},
            1 => {"a".into(), "b".into()},
            2 => {"b".into()},
            3 => {"a".into()}
        };

        let ts = TransitionSystem::new(
            &states,
            &initial_states,
            &transitions,
            &transitions_back,
            &label,
        );

        // sat(true)
        assert_eq!(
            ts.sat(&Enf::True),
            states
        );

        // sat("a")
        assert_eq!(
            ts.sat(
                &Enf::Prop("a".into())
            ),
            set! {0, 1, 3}
        );

        // sat("a" and "b")
        assert_eq!(
            ts.sat(
                &Enf::And(
                    &Enf::Prop("a".into()),
                    &Enf::Prop("b".into()),
                )
            ),
            set! {1}
        );

        // sat(not "b")
        assert_eq!(
            ts.sat(
                &Enf::Not(
                    &Enf::Prop("b".into())
                )
            ),
            set! {0, 3}
        );

        // sat(exists next "a")
        assert_eq!(
            ts.sat(
                &Enf::ExistsNext(
                    &Enf::Prop("a".into())
                )
            ),
            set! {0, 1, 2, 3}
        );

        // sat(exists ("a" until "b"))
        assert_eq!(
            ts.sat(
                &Enf::ExistsUntil(
                    &Enf::Prop("a".into()),
                    &Enf::Prop("b".into()),
                )
            ),
            set! {0, 1}
        );

        // sat(exists ("a" until "a"))
        assert_eq!(
            ts.sat(
                &Enf::ExistsUntil(
                    &Enf::Prop("a".into()),
                    &Enf::Prop("a".into()),
                )
            ),
            set! {0, 1, 3}
        );
    }
}