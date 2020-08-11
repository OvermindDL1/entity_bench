use criterion::{black_box, criterion_group, criterion_main, Criterion};
use entity_bench::SparseSet;
use std::sync::{Arc, RwLock};

mod LinearLocked {
    #[derive(Default)]
    pub struct EntityRegistry {
        /// `entities` is interesting in that alive ones have their internal index
        /// match their actual index, if it's dead they don't.  If it's dead the
        /// internal index actually points to the actual index of the next 'dead'
        /// one, thus making a handle-based link-list.  If it points to
        /// `0` then there are no more dead entities and a new one needs to be
        /// created.  The generation gets incremented on destruction.
        pub entities: Vec<u64>,
        /// This is the 'head' of the singly-linked list of destroyed entities.
        pub destroyed: u64,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: Vec::with_capacity(cap),
                destroyed: 0,
            }
        }
        pub fn create(&mut self) -> u64 {
            if self.destroyed == 0 {
                // `destroyed` linked list is empty
                let entity = self.entities.len() as u64;
                self.entities.push(entity);
                entity
            } else {
                let head = self.destroyed;
                // TODO:  This should be safe to make unsafe and use `get_unchecked`
                let head_entity = &mut self.entities[head as usize];
                self.destroyed = *head_entity & 0x0000_0000_FFFF_FFFF; // New head of destroyed list
                *head_entity = (*head_entity & 0x0000_0000_FFFF_FFFF) + head;
                *head_entity
            }
        }
    }
}

mod LinearAtomic {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::RwLock;

    pub struct EntityRegistry {
        pub entities: RwLock<Vec<AtomicU64>>,
        pub dead: crossbeam::deque::Worker<u64>,
    }

    impl Default for EntityRegistry {
        fn default() -> Self {
            EntityRegistry {
                entities: Default::default(),
                dead: crossbeam::deque::Worker::new_lifo(),
            }
        }
    }

    impl EntityRegistry {
        pub fn create(&mut self) -> u64 {
            match self.dead.pop() {
                Some(id) => {
                    let idx = (id & 0x0000_0000_FFFF_FFFF);
                    let entity = idx + ((id & 0xFFFF_FFFF_0000_0000) + 0x0000_0001_0000_0000);
                    self.entities.write().unwrap()[idx as usize].store(entity, Ordering::Relaxed);
                    entity
                }
                None => {
                    let mut entities = self.entities.write().unwrap();
                    let entity = entities.len() as u64;
                    entities.push(AtomicU64::new(entity));
                    entity
                }
            }
        }
    }
}

mod Random {
    use std::collections::HashMap;
    use std::sync::RwLock;

    #[derive(Default)]
    pub struct EntityRegistry {
        pub entities: HashMap<u32, ()>,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: HashMap::with_capacity(cap),
            }
        }
        pub fn create(&mut self) -> u32 {
            let entity: u32 = rand::random();
            self.entities.insert(entity, ());
            entity
        }
    }
}

mod RandomSparse {
    use entity_bench::SparseSet;
    use std::sync::RwLock;

    #[derive(Default)]
    pub struct EntityRegistry {
        pub entities: SparseSet<u64, ()>,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: SparseSet::with_capacity(cap),
            }
        }
        pub fn create(&mut self) -> u32 {
            let entity: u32 = rand::random();
            self.entities.insert(entity as u64, ());
            entity
        }
    }
}

mod random_ahash {
    use hashbrown::HashMap;
    use std::sync::RwLock;

    #[derive(Default)]
    pub struct EntityRegistry {
        pub entities: HashMap<u64, ()>,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: HashMap::with_capacity(cap),
            }
        }
        pub fn create(&mut self) -> u32 {
            let entity: u32 = rand::random();
            self.entities.insert(entity as u64, ());
            entity
        }
    }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    {
        let mut c = c.benchmark_group("create");
        c.bench_function("create-linear", |b| {
            let mut reg = LinearLocked::EntityRegistry::new(1_000_000);
            b.iter(|| {
                black_box(reg.create());
            });
            black_box(reg.entities.len());
        });
        c.bench_function("create-linear-locked", |b| {
            let mut reg = RwLock::new(LinearLocked::EntityRegistry::new(1_000_000));
            b.iter(|| {
                black_box(reg.write().unwrap().create());
            });
            black_box(reg.read().unwrap().entities.len());
        });
        c.bench_function("create-linear-atomic", |b| {
            let mut reg = LinearAtomic::EntityRegistry::default();
            b.iter(|| {
                black_box(reg.create());
            });
        });
        c.bench_function("create-rand", |b| {
            let mut reg = Random::EntityRegistry::new(1_000_000);
            b.iter(|| {
                black_box(reg.create());
            });
            black_box(reg.entities.len());
        });
        c.bench_function("create-rand-sparse", |b| {
            let mut reg = RandomSparse::EntityRegistry::new(0);
            b.iter(|| {
                black_box(reg.create());
            });
            black_box(reg.entities.len());
        });
        c.bench_function("create-rand-ahash", |b| {
            let mut reg = random_ahash::EntityRegistry::new(0);
            b.iter(|| {
                black_box(reg.create());
            });
            black_box(reg.entities.len());
        });
        c.bench_function("create-rand-locked", |b| {
            let mut reg = RwLock::new(Random::EntityRegistry::new(1_000_000));
            b.iter(|| {
                black_box(reg.write().unwrap().create());
            });
            black_box(reg.read().unwrap().entities.len());
        });
        c.bench_function("create-rand-by-itself", |b| {
            b.iter(|| {
                let entity: u128 = black_box(rand::random());
                black_box(entity);
            });
        });
    }
    {
        let mut c = c.benchmark_group("get");
        c.bench_function("sparsemap", |b| {
            let mut map = SparseSet::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                black_box(map.get(black_box(42)));
            });
            black_box(map.len());
        });
        c.bench_function("hashmap", |b| {
            let mut map = std::collections::HashMap::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                black_box(map.get(black_box(&42)));
            });
            black_box(map.len());
        });
        c.bench_function("ahashmap", |b| {
            let mut map = hashbrown::HashMap::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                black_box(map.get(black_box(&42)));
            });
            black_box(map.len());
        });
    }
    {
        let mut c = c.benchmark_group("iterate");
        c.bench_function("sparsemap", |b| {
            let mut map = SparseSet::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                for entity in map.entities() {
                    black_box(entity);
                }
            });
            black_box(map.len());
        });
        c.bench_function("hashmap", |b| {
            let mut map = std::collections::HashMap::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                for entity in map.keys() {
                    black_box(entity);
                }
            });
            black_box(map.len());
        });
        c.bench_function("ahashmap", |b| {
            let mut map = hashbrown::HashMap::new();
            for entity in 0..1_000u64 {
                map.insert(entity, ());
            }
            b.iter(|| {
                for entity in map.keys() {
                    black_box(entity);
                }
            });
            black_box(map.len());
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
