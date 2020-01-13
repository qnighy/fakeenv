# fakeenv

A simple wrapper of `std::env` which allows faking the environment.

[`std::env`]: https://doc.rust-lang.org/std/env/index.html

# Example

## Using the real environment

```
use fakeenv::EnvStore;

fn answer(env: &EnvStore) -> i32 {
    env.var("THE_ANSWER").unwrap().parse().unwrap()
}

fn main() {
    std::env::set_var("THE_ANSWER", "42");

    let env = EnvStore::real();
    assert_eq!(answer(&env), 42);
}
```

## Making a fake environment

Fake is only turned on when the `fake` feature is enabled.

As this is mostly for testing purpose, you might want to enable
the feature like this:

```toml
[dependencies]
fakeenv = "0.1.0"

[dev-dependencies]
fakeenv = { version = "0.1.0", features = ["fake"] }
```

Then you can generate a fake environment using [`EnvStore::fake`]:

[`EnvStore::fake`]: struct.EnvStore.html#method.fake

```
use fakeenv::EnvStore;

fn answer(env: &EnvStore) -> i32 {
    env.var("THE_ANSWER").unwrap().parse().unwrap()
}

fn main() {
    let env = EnvStore::fake();
    env.set_var("THE_ANSWER", "42");
    assert_eq!(answer(&env), 42);
}
```
