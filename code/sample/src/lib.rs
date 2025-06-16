pub struct Counter {
    pub count: u64,
    pub step: u64,
}


impl Counter {
    pub fn new() -> Self {
        Counter { count: 0, step: 1 }
    }

    pub fn increment(&mut self) {
        self.count += self.step;
    }

    pub fn reset(&mut self) {
        self.count = 0;
    }

    pub fn set_step(&mut self, step: u64) {
        self.step = step;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_counter() {
        let mut counter = Counter::new();

        counter.increment();
        assert_eq!(counter.count, 1);

        counter.set_step(2);
        counter.increment();
        assert_eq!(counter.count, 3);

        counter.reset();
        assert_eq!(counter.count, 0);
    }
}