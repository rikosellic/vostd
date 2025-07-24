pub struct Counter {
    pub count: u64,
    pub step: u64,
}


impl Counter {
    pub fn new() -> Self {
        Counter { count: 0, step: 1 }
    }

    pub fn get_count(&self) -> u64 {
        self.count
    }

    pub fn get_step(&self) -> u64 {
        self.step
    }

    pub fn reset(&mut self) {
        self.count = 0;
    }

    pub fn set_step(&mut self, step: u64) {
        // ensure the step is not zero to avoid infinite loops
        if step != 0 {
            self.step = step;
        }
    }

    pub fn increment(&mut self) {
        // make the wrapping behavior more explicit
        if self.get_count() > u64::MAX - self.get_step() {
            self.count = 0;
        } else {
            self.count = self.get_count() + self.get_step();
        }
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

    #[test]
    fn test_counter_wrap() {
        let mut counter = Counter::new();
        counter.set_step(u64::MAX);
        counter.increment();
        assert_eq!(counter.count, u64::MAX);

        counter.increment(); // This should wrap around
        assert_eq!(counter.count, 0);
    }
}