//! A simple wrapper of `std::env` which allows faking the environment.
//!
//! [`std::env`]: https://doc.rust-lang.org/std/env/index.html
//!
//! # Example
//!
//! ## Using the real environment
//!
//! ```
//! use fakeenv::EnvStore;
//!
//! fn answer(env: &EnvStore) -> i32 {
//!     env.var("THE_ANSWER").unwrap().parse().unwrap()
//! }
//!
//! fn main() {
//!     std::env::set_var("THE_ANSWER", "42");
//!
//!     let env = EnvStore::real();
//!     assert_eq!(answer(&env), 42);
//! }
//! ```
//!
//! ## Making a fake environment
//!
//! Fake is only turned on when the `fake` feature is enabled.
//!
//! As this is mostly for testing purpose, you might want to enable
//! the feature like this:
//!
//! ```toml
//! [dependencies]
//! fakeenv = "0.1.0"
//!
//! [dev-dependencies]
//! fakeenv = { version = "0.1.0", features = ["fake"] }
//! ```
//!
//! Then you can generate a fake environment using [`EnvStore::fake`]:
//!
//! [`EnvStore::fake`]: struct.EnvStore.html#method.fake
//!
//! ```
//! use fakeenv::EnvStore;
//!
//! fn answer(env: &EnvStore) -> i32 {
//!     env.var("THE_ANSWER").unwrap().parse().unwrap()
//! }
//!
//! # #[cfg(feature = "fake")]
//! fn main() {
//!     let env = EnvStore::fake();
//!     env.set_var("THE_ANSWER", "42");
//!     assert_eq!(answer(&env), 42);
//! }
//! # #[cfg(not(feature = "fake"))]
//! # fn main() {}
//! ```

#![cfg_attr(feature = "__doc_cfg", feature(doc_cfg))]
#![warn(missing_docs)]

use std::env;
use std::ffi::{OsStr, OsString};
use std::io;
use std::panic::{RefUnwindSafe, UnwindSafe};
use std::path::{Path, PathBuf};

#[cfg(feature = "fake")]
use std::collections::{hash_map, HashMap};
#[cfg(feature = "fake")]
use std::sync::{Arc, RwLock};

pub use std::env::VarError;

/// A handle to either the real environment or a fake environment.
///
/// # Example
///
/// ## Using the real environment
///
/// ```
/// # use fakeenv::EnvStore;
/// let env = EnvStore::real();
/// std::env::set_var("THE_ANSWER", "42");
/// assert_eq!(env.var("THE_ANSWER").unwrap(), "42");
/// ```
///
/// ## Making a fake environment
///
/// ```
/// # #[cfg(feature = "fake")]
/// # {
/// # use fakeenv::EnvStore;
/// let env = EnvStore::fake();
/// env.set_var("THE_ANSWER", "42");
/// assert_eq!(env.var("THE_ANSWER").unwrap(), "42");
/// # }
/// ```
///
/// # Cloning
///
/// The `Clone` implementation does the shallow copy, whereas the
/// [`EnvStore::to_fake`] method does the deep copy.
///
/// [`EnvStore::to_fake`]: #method.to_fake
///
/// ```
/// # #[cfg(feature = "fake")]
/// # {
/// # use fakeenv::EnvStore;
/// let env = EnvStore::fake();
/// env.set_var("X", "42");
///
/// let env2 = env.to_fake();
/// env2.set_var("X", "53");
/// // The original env doesn't change
/// assert_eq!(env.var("X").unwrap(), "42");
///
/// let env3 = env.clone();
/// env3.set_var("X", "84");
/// // The original env changes as well
/// assert_eq!(env.var("X").unwrap(), "84");
/// # }
/// ```
///
/// # Default
///
/// The `Default` implementation is equivalent to [`EnvStore::real`].
///
/// [`EnvStore::real`]: #method.real
#[derive(Debug, Clone)]
pub struct EnvStore {
    kind: EnvStoreKind,
}

// Without this, `EnvStore` would be `UnwindSafe + RefUnwindSafe`
// when `cfg(not(feature = "fake"))` but not when `cfg(feature = "fake")`.
impl UnwindSafe for EnvStore {}
impl RefUnwindSafe for EnvStore {}

impl EnvStore {
    /// Returns the handle to the real environment.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    /// std::env::set_var("THE_ANSWER", "42");
    /// assert_eq!(env.var("THE_ANSWER").unwrap(), "42");
    /// ```
    pub const fn real() -> Self {
        Self {
            kind: EnvStoreKind::Real,
        }
    }

    /// Creates a new fake environment from the real environment.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::fake();
    /// env.set_var("THE_ANSWER", "42");
    /// assert_eq!(env.var("THE_ANSWER").unwrap(), "42");
    /// ```
    #[cfg(feature = "fake")]
    #[cfg_attr(feature = "__doc_cfg", doc(cfg(feature = "fake")))]
    pub fn fake() -> Self {
        Self::real().to_fake()
    }

    /// Creates a new fake environment from the existing environment (real or fake).
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::fake();
    /// env.set_var("THE_ANSWER", "42");
    ///
    /// let env2 = env.to_fake();
    /// env2.set_var("THE_ANSWER", "84");
    ///
    /// assert_eq!(env2.var("THE_ANSWER").unwrap(), "84");
    /// assert_eq!(env.var("THE_ANSWER").unwrap(), "42");
    /// ```
    #[cfg(feature = "fake")]
    #[cfg_attr(feature = "__doc_cfg", doc(cfg(feature = "fake")))]
    pub fn to_fake(&self) -> Self {
        let inner = match &self.kind {
            EnvStoreKind::Real => {
                let current_dir = env::current_dir().ok();
                let vars = env::vars_os().collect::<HashMap<_, _>>();
                EnvStoreInner { current_dir, vars }
            }
            EnvStoreKind::Fake(inner) => {
                let inner = inner.read().unwrap();
                inner.clone()
            }
        };
        let inner = Arc::new(RwLock::new(inner));
        Self {
            kind: EnvStoreKind::Fake(inner),
        }
    }

    /// Returns `true` if this is the real environment.
    pub fn is_real(&self) -> bool {
        match &self.kind {
            EnvStoreKind::Real => true,
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(_) => false,
        }
    }

    /// Returns `true` if this is a fake environment.
    pub fn is_fake(&self) -> bool {
        !self.is_real()
    }

    /// Returns whether the two handle points to the same environment.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        match &self.kind {
            EnvStoreKind::Real => match &other.kind {
                EnvStoreKind::Real => true,
                #[cfg(feature = "fake")]
                EnvStoreKind::Fake(_) => false,
            },
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => match &other.kind {
                EnvStoreKind::Real => false,
                EnvStoreKind::Fake(inner_other) => Arc::ptr_eq(inner, inner_other),
            },
        }
    }

    /// Fetches the environment variable `key` from the current process.
    /// Corresponds with [`std::env::var`].
    ///
    /// [`std::env::var`]: https://doc.rust-lang.org/std/env/fn.var.html
    ///
    /// # Errors
    ///
    /// - Environment variable is not present
    /// - Environment variable is not valid unicode
    ///
    /// # Panics
    ///
    /// This function may panic if `key` is empty, contains an ASCII equals
    /// sign `'='` or the NUL character `'\0'`, or when the value contains the
    /// NUL character.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// let key = "HOME";
    /// match env.var(key) {
    ///     Ok(val) => println!("{}: {:?}", key, val),
    ///     Err(e) => println!("couldn't interpret {}: {}", key, e),
    /// }
    /// ```
    pub fn var<K: AsRef<OsStr>>(&self, key: K) -> Result<String, VarError> {
        self.var_inner(key.as_ref())
    }

    fn var_inner(&self, key: &OsStr) -> Result<String, VarError> {
        let value = self.var_os_inner(key).ok_or(VarError::NotPresent)?;
        value.into_string().map_err(VarError::NotUnicode)
    }

    /// Fetches the environment variable `key` from the current process,
    /// returning [`None`] if the variable isn't set.
    /// Corresponds with [`std::env::var_os`].
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`std::env::var_os`]: https://doc.rust-lang.org/std/env/fn.var_os.html
    ///
    /// # Panics
    ///
    /// This function may panic if `key` is empty, contains an ASCII equals
    /// sign `'='` or the NUL character `'\0'`, or when the value contains the
    /// NUL character.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// let key = "HOME";
    /// match env.var_os(key) {
    ///     Some(val) => println!("{}: {:?}", key, val),
    ///     None => println!("{} is not defined in the environment.", key)
    /// }
    /// ```
    pub fn var_os<K: AsRef<OsStr>>(&self, key: K) -> Option<OsString> {
        self.var_os_inner(key.as_ref())
    }

    fn var_os_inner(&self, key: &OsStr) -> Option<OsString> {
        match &self.kind {
            EnvStoreKind::Real => env::var_os(key),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let inner = inner.read().unwrap();
                inner.vars.get(key).cloned()
            }
        }
    }

    /// Returns an iterator of (variable, value) pairs of strings, for all the
    /// environment variables of the current process.
    /// Corresponds with [`std::env::vars`].
    ///
    /// [`std::env::vars`]: https://doc.rust-lang.org/std/env/fn.vars.html
    ///
    /// The returned iterator contains a snapshot of the process's environment
    /// variables at the time of this invocation. Modifications to environment
    /// variables afterwards will not be reflected in the returned iterator.
    ///
    /// # Panics
    ///
    /// While iterating, the returned iterator will panic if any key or value
    /// in the environment is not valid unicode. If this is not desired,
    /// consider using the [`EnvStore::vars_os`] method.
    ///
    /// [`EnvStore::vars_os`]: #method.vars_os
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// // We will iterate through the references to the element returned by
    /// // env::vars();
    /// for (key, value) in env.vars() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    pub fn vars(&self) -> Vars {
        Vars {
            inner: self.vars_os(),
        }
    }

    /// Returns an iterator of (variable, value) pairs of OS strings, for all
    /// the environment variables of the current process.
    /// Corresponds with [`std::env::vars_os`].
    ///
    /// [`std::env::vars_os`]: https://doc.rust-lang.org/std/env/fn.vars_os.html
    ///
    /// The returned iterator contains a snapshot of the process's environment
    /// variables at the time of this invocation. Modifications to environment
    /// variables afterwards will not be reflected in the returned iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// // We will iterate through the references to the element returned by
    /// // env.vars_os();
    /// for (key, value) in env.vars_os() {
    ///     println!("{:?}: {:?}", key, value);
    /// }
    /// ```
    pub fn vars_os(&self) -> VarsOs {
        let kind = match &self.kind {
            EnvStoreKind::Real => VarsOsKind::Real(env::vars_os()),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let inner = inner.read().unwrap();
                VarsOsKind::Fake(inner.vars.clone().into_iter())
            }
        };
        VarsOs { kind }
    }

    /// Sets the environment variable `k` to the value `v` for the currently
    /// running process.
    /// Corresponds with [`std::env::set_var`].
    ///
    /// [`std::env::set_var`]: https://doc.rust-lang.org/std/env/fn.set_var.html
    ///
    /// Note that while concurrent access to environment variables is safe in
    /// Rust, some platforms only expose inherently unsafe non-threadsafe APIs
    /// for inspecting the environment. As a result, extra care needs to be
    /// taken when auditing calls to unsafe external FFI functions to ensure
    /// that any external environment accesses are properly synchronized with
    /// accesses in Rust.
    ///
    /// Discussion of this unsafety on Unix may be found in:
    ///
    ///  - [Austin Group Bugzilla](http://austingroupbugs.net/view.php?id=188)
    ///  - [GNU C library Bugzilla](https://sourceware.org/bugzilla/show_bug.cgi?id=15607#c2)
    ///
    /// # Panics
    ///
    /// This function may panic if `key` is empty, contains an ASCII equals
    /// sign `'='` or the NUL character `'\0'`, or when the value contains the
    /// NUL character.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// let key = "KEY";
    /// env.set_var(key, "VALUE");
    /// assert_eq!(env.var(key), Ok("VALUE".to_string()));
    /// ```
    pub fn set_var<K: AsRef<OsStr>, V: AsRef<OsStr>>(&self, k: K, v: V) {
        self.set_var_inner(k.as_ref(), v.as_ref())
    }

    fn set_var_inner(&self, k: &OsStr, v: &OsStr) {
        match &self.kind {
            EnvStoreKind::Real => env::set_var(k, v),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let k = k.to_owned();
                let v = v.to_owned();
                let mut inner = inner.write().unwrap();
                inner.vars.insert(k, v);
            }
        }
    }

    /// Removes an environment variable from the environment of the currently
    /// running process.
    /// Corresponds with [`std::env::remove_var`].
    ///
    /// [`std::env::remove_var`]: https://doc.rust-lang.org/std/env/fn.remove_var.html
    ///
    /// Note that while concurrent access to environment variables is safe in
    /// Rust, some platforms only expose inherently unsafe non-threadsafe APIs
    /// for inspecting the environment. As a result extra care needs to be
    /// taken when auditing calls to unsafe external FFI functions to ensure
    /// that any external environment accesses are properly synchronized with
    /// accesses in Rust.
    ///
    /// Discussion of this unsafety on Unix may be found in:
    ///
    ///  - [Austin Group Bugzilla](http://austingroupbugs.net/view.php?id=188)
    ///  - [GNU C library Bugzilla](https://sourceware.org/bugzilla/show_bug.cgi?id=15607#c2)
    ///
    /// # Panics
    ///
    /// This function may panic if `key` is empty, contains an ASCII equals
    /// sign `'='` or the NUL character `'\0'`, or when the value contains the
    /// NUL character.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fakeenv::EnvStore;
    /// let env = EnvStore::real();
    ///
    /// let key = "KEY";
    /// env.set_var(key, "VALUE");
    /// assert_eq!(env.var(key), Ok("VALUE".to_string()));
    ///
    /// env.remove_var(key);
    /// assert!(env.var(key).is_err());
    /// ```
    pub fn remove_var<K: AsRef<OsStr>>(&self, k: K) {
        self.remove_var_inner(k.as_ref())
    }

    fn remove_var_inner(&self, k: &OsStr) {
        match &self.kind {
            EnvStoreKind::Real => env::remove_var(k),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let mut inner = inner.write().unwrap();
                inner.vars.remove(k);
            }
        }
    }

    /// Returns the current working directory as a [`PathBuf`].
    /// Corresponds with [`std::env::current_dir`].
    ///
    /// [`std::env::current_dir`]: https://doc.rust-lang.org/std/env/fn.current_dir.html
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the current working directory value is invalid.
    /// Possible cases:
    ///
    /// * Current directory does not exist.
    /// * There are insufficient permissions to access the current directory.
    ///
    /// [`PathBuf`]: https://doc.rust-lang.org/std/path/struct.PathBuf.html
    /// [`Err`]: https://doc.rust-lang.org/std/result/enum.Result.html#method.err
    ///
    /// # Examples
    ///
    /// ```
    /// use fakeenv::EnvStore;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let env = EnvStore::real();
    ///
    ///     let path = env.current_dir()?;
    ///     println!("The current directory is {}", path.display());
    ///     Ok(())
    /// }
    /// ```
    pub fn current_dir(&self) -> io::Result<PathBuf> {
        match &self.kind {
            EnvStoreKind::Real => env::current_dir(),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let inner = inner.read().unwrap();
                inner.current_dir.clone().ok_or_else(|| {
                    io::Error::new(io::ErrorKind::NotFound, "current directory not found")
                })
            }
        }
    }

    /// Changes the current working directory to the specified path.
    /// Corresponds with [`std::env::set_current_dir`].
    ///
    /// [`std::env::set_current_dir`]: https://doc.rust-lang.org/std/env/fn.set_current_dir.html
    ///
    /// Returns an [`Err`] if the operation fails.
    ///
    /// [`Err`]: https://doc.rust-lang.org/std/result/enum.Result.html#method.err
    ///
    /// # Examples
    ///
    /// ```
    /// use fakeenv::EnvStore;
    /// use std::path::Path;
    ///
    /// let env = EnvStore::real();
    ///
    /// let root = Path::new("/");
    /// assert!(env.set_current_dir(&root).is_ok());
    /// println!("Successfully changed working directory to {}!", root.display());
    /// ```
    pub fn set_current_dir<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        self.set_current_dir_inner(path.as_ref())
    }

    fn set_current_dir_inner(&self, path: &Path) -> io::Result<()> {
        match &self.kind {
            EnvStoreKind::Real => env::set_current_dir(path),
            #[cfg(feature = "fake")]
            EnvStoreKind::Fake(inner) => {
                let mut inner = inner.write().unwrap();
                inner.current_dir = Some(path.to_owned());
                Ok(())
            }
        }
    }
}

impl Default for EnvStore {
    fn default() -> Self {
        Self::real()
    }
}

#[derive(Debug, Clone)]
enum EnvStoreKind {
    Real,
    #[cfg(feature = "fake")]
    Fake(Arc<RwLock<EnvStoreInner>>),
}

#[cfg(feature = "fake")]
#[derive(Debug, Clone)]
struct EnvStoreInner {
    current_dir: Option<PathBuf>,
    vars: HashMap<OsString, OsString>,
}

/// An iterator over a snapshot of the environment variables of this process.
///
/// This structure is created by the [`EnvStore::vars`] function. See its
/// documentation for more.
///
/// [`EnvStore::vars`]: struct.EnvStore.html#method.vars
#[derive(Debug)]
pub struct Vars {
    inner: VarsOs,
}

impl Iterator for Vars {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|(a, b)| (a.into_string().unwrap(), b.into_string().unwrap()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over a snapshot of the environment variables of this process.
///
/// This structure is created by the [`EnvStore::vars_os`] function. See
/// its documentation for more.
///
/// [`EnvStore::vars_os`]: struct.EnvStore.html#method.vars_os
#[derive(Debug)]
pub struct VarsOs {
    kind: VarsOsKind,
}

impl Iterator for VarsOs {
    type Item = (OsString, OsString);
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.kind {
            VarsOsKind::Real(inner) => inner.next(),
            #[cfg(feature = "fake")]
            VarsOsKind::Fake(inner) => inner.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.kind {
            VarsOsKind::Real(inner) => inner.size_hint(),
            #[cfg(feature = "fake")]
            VarsOsKind::Fake(inner) => inner.size_hint(),
        }
    }
}

#[derive(Debug)]
enum VarsOsKind {
    Real(env::VarsOs),
    #[cfg(feature = "fake")]
    Fake(hash_map::IntoIter<OsString, OsString>),
}
