fn greet(name: String) -> IO<Unit> {
    do {
        print("hello, ");
        println(name)
    }
}

fn ask() -> IO<Nat> { pure(41) }

fn main() -> IO<Unit> {
    do {
        let n <- ask();
        greet("world");
        println(Nat.toString(n + 1))
    }
}

theorem strings_are_values(): "a" = "a" := rfl
