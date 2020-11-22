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
