mod routine;
use std::collections::HashMap;
use std::sync::Arc;
use routine::{Routine, BUILT_INS, initialize_built_ins};

pub struct StdLib {
    routines: HashMap<String, Routine>,
}

impl StdLib {
    pub fn new() -> Self {
        let mut routines = HashMap::new();
        // No thread-concurrency problem for the access to `BUILT_INS`, as the whole interpreter is single-thread for now
        let built_ins = BUILT_INS.get_or_init(initialize_built_ins);
        for (name, routine) in built_ins {
            routines.insert(name.to_owned().to_owned(), Routine {ptr: Arc::clone(&Arc::clone(routine))});
        }
        StdLib { routines }
    }

    pub fn get_routine(&self, name: &String) -> Option<&Routine> {
        self.routines.get(name)
    }
}