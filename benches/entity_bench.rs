use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};

mod linear {
    use entity_bench::Entity;

    #[derive(Default)]
    pub struct EntityRegistry<EntityType: Entity> {
        /// `entities` is interesting in that alive ones have their internal index
        /// match their actual index, if it's dead they don't.  If it's dead the
        /// internal index actually points to the actual index of the next 'dead'
        /// one, thus making a handle-based link-list.  If it points to
        /// `0` then there are no more dead entities and a new one needs to be
        /// created.  The generation gets incremented on destruction.
        pub entities: Vec<EntityType>,
        /// This is the 'head' of the singly-linked list of destroyed entities.
        pub destroyed: EntityType,
    }

    impl<EntityType: Entity> EntityRegistry<EntityType> {
        pub fn new(cap: usize) -> EntityRegistry<EntityType> {
            let mut registry = EntityRegistry {
                entities: Vec::with_capacity(cap),
                destroyed: EntityType::new(0),
            };
            registry.entities.push(EntityType::new(0)); // First is the null entity
            registry
        }

        pub fn create(&mut self) -> EntityType {
            if self.destroyed.is_null() {
                // `destroyed` linked list is empty
                let entity = EntityType::new(self.entities.len());
                self.entities.push(entity);
                entity
            } else {
                let head = self.destroyed.idx();
                // TODO:  This should be safe to make unsafe and use `get_unchecked`
                let head_entity = &mut self.entities[head];
                self.destroyed = EntityType::new(head_entity.idx()); // New head of destroyed list
                *head_entity.set_idx(head)
            }
        }
    }
}

mod random_hashmap {
    use std::collections::HashMap;

    #[derive(Default)]
    pub struct EntityRegistry {
        pub entities: HashMap<u128, ()>,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: HashMap::with_capacity(cap),
            }
        }

        pub fn create(&mut self) -> u128 {
            let entity: u128 = rand::random();
            self.entities.insert(entity, ());
            entity
        }
    }
}

mod random_ahash {
    use hashbrown::HashMap;

    #[derive(Default)]
    pub struct EntityRegistry {
        pub entities: HashMap<u128, ()>,
    }

    impl EntityRegistry {
        pub fn new(cap: usize) -> EntityRegistry {
            EntityRegistry {
                entities: HashMap::with_capacity(cap),
            }
        }

        pub fn create(&mut self) -> u128 {
            let entity: u128 = rand::random();
            self.entities.insert(entity, ());
            entity
        }
    }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    {
        let mut c = c.benchmark_group("create");
        c.bench_function("create-linear-u32", |b| {
            b.iter_batched_ref(
                || linear::EntityRegistry::<u32>::new(32),
                |reg| black_box(reg.create()),
                BatchSize::LargeInput,
            );
        });
        c.bench_function("create-linear-u64", |b| {
            b.iter_batched_ref(
                || linear::EntityRegistry::<u64>::new(32),
                |reg| black_box(reg.create()),
                BatchSize::LargeInput,
            );
        });
        c.bench_function("create-linear-u128", |b| {
            b.iter_batched_ref(
                || linear::EntityRegistry::<u128>::new(32),
                |reg| black_box(reg.create()),
                BatchSize::LargeInput,
            );
        });
        c.bench_function("create-u128-rand-hashmap", |b| {
            b.iter_batched_ref(
                || random_hashmap::EntityRegistry::new(32),
                |reg| black_box(reg.create()),
                BatchSize::LargeInput,
            );
        });
        c.bench_function("create-u128-rand-ahash", |b| {
            b.iter_batched_ref(
                || random_ahash::EntityRegistry::new(32),
                |reg| black_box(reg.create()),
                BatchSize::LargeInput,
            );
        });
        c.bench_function("create-u128-rand-by-itself", |b| {
            b.iter(|| {
                let entity: u128 = black_box(rand::random());
                black_box(entity);
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
