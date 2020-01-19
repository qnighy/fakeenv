use std::path::PathBuf;

#[cfg(feature = "fake")]
use std::path::Path;

use crate::{EnvStore, EnvStoreKind};

#[cfg(feature = "fake")]
#[derive(Debug, Clone)]
pub(crate) struct DirsStore {
    audio_dir: Option<PathBuf>,
    cache_dir: Option<PathBuf>,
    config_dir: Option<PathBuf>,
    data_dir: Option<PathBuf>,
    data_local_dir: Option<PathBuf>,
    desktop_dir: Option<PathBuf>,
    document_dir: Option<PathBuf>,
    download_dir: Option<PathBuf>,
    executable_dir: Option<PathBuf>,
    font_dir: Option<PathBuf>,
    home_dir: Option<PathBuf>,
    picture_dir: Option<PathBuf>,
    public_dir: Option<PathBuf>,
    runtime_dir: Option<PathBuf>,
    template_dir: Option<PathBuf>,
    video_dir: Option<PathBuf>,
}

#[cfg(feature = "fake")]
impl DirsStore {
    pub(crate) fn from_real() -> Self {
        Self {
            audio_dir: dirs::audio_dir(),
            cache_dir: dirs::cache_dir(),
            config_dir: dirs::config_dir(),
            data_dir: dirs::data_dir(),
            data_local_dir: dirs::data_local_dir(),
            desktop_dir: dirs::desktop_dir(),
            document_dir: dirs::document_dir(),
            download_dir: dirs::download_dir(),
            executable_dir: dirs::executable_dir(),
            font_dir: dirs::font_dir(),
            home_dir: dirs::home_dir(),
            picture_dir: dirs::picture_dir(),
            public_dir: dirs::public_dir(),
            runtime_dir: dirs::runtime_dir(),
            template_dir: dirs::template_dir(),
            video_dir: dirs::video_dir(),
        }
    }
}

macro_rules! define_dirs_methods {
    (
        $((
            $name:ident,
            $setter:ident,
            $unsetter:ident
        ),)*
    ) => {
        $(
            /// Returns the path to the directory. See [`dirs`] for details.
            ///
            /// [`dirs`]: https://docs.rs/dirs/2.*/dirs/index.html
            ///
            /// ## Examples
            ///
            /// ```rust
            /// # use fakeenv::EnvStore;
            /// let env = EnvStore::real();
            /// println!("home directory = {:?}", env.home_dir());
            /// ```
            #[cfg_attr(feature = "__doc_cfg", doc(cfg(feature = "dirs")))]
            pub fn $name(&self) -> Option<PathBuf> {
                match &self.kind {
                    EnvStoreKind::Real => dirs::$name(),
                    #[cfg(feature = "fake")]
                    EnvStoreKind::Fake(inner) => {
                        let inner = inner.read().unwrap();
                        inner.dirs.$name.clone()
                    }
                }
            }

            /// Modifies the faked path to the directory. See [`dirs`] for details.
            ///
            /// [`dirs`]: https://docs.rs/dirs/2.*/dirs/index.html
            ///
            /// ## Panics
            ///
            /// This method panics when `self` points to the real environment.
            ///
            /// ## Examples
            ///
            /// ```rust
            /// # use std::path::Path;
            /// # use fakeenv::EnvStore;
            /// let env = EnvStore::fake();
            /// env.set_home_dir("/foo/bar");
            /// assert_eq!(&env.home_dir().unwrap(), Path::new("/foo/bar"));
            /// ```
            #[cfg(feature = "fake")]
            #[cfg_attr(feature = "__doc_cfg", doc(cfg(all(feature = "dirs", feature = "fake"))))]
            pub fn $setter<P: AsRef<Path>>(&self, path: P) {
                match &self.kind {
                    EnvStoreKind::Real => panic!("EnvStore::{} cannot modify the real environment", stringify!($setter)),
                    EnvStoreKind::Fake(inner) => {
                        let path = path.as_ref().to_owned();
                        let mut inner = inner.write().unwrap();
                        inner.dirs.$name = Some(path);
                    }
                }
            }

            /// Modifies the faked path to the directory. See [`dirs`] for details.
            ///
            /// [`dirs`]: https://docs.rs/dirs/2.*/dirs/index.html
            ///
            /// ## Panics
            ///
            /// This method panics when `self` points to the real environment.
            ///
            /// ## Examples
            ///
            /// ```rust
            /// # use fakeenv::EnvStore;
            /// let env = EnvStore::fake();
            /// env.unset_home_dir();
            /// assert!(env.home_dir().is_none());
            /// ```
            #[cfg(feature = "fake")]
            #[cfg_attr(feature = "__doc_cfg", doc(cfg(all(feature = "dirs", feature = "fake"))))]
            pub fn $unsetter(&self) {
                match &self.kind {
                    EnvStoreKind::Real => panic!("EnvStore::{} cannot modify the real environment", stringify!($setter)),
                    EnvStoreKind::Fake(inner) => {
                        let mut inner = inner.write().unwrap();
                        inner.dirs.$name = None;
                    }
                }
            }
        )*
    };
}

#[cfg(feature = "dirs")]
impl EnvStore {
    define_dirs_methods!(
        (audio_dir, set_audio_dir, unset_audio_dir),
        (cache_dir, set_cache_dir, unset_cache_dir),
        (config_dir, set_config_dir, unset_config_dir),
        (data_dir, set_data_dir, unset_data_dir),
        (data_local_dir, set_data_local_dir, unset_data_local_dir),
        (desktop_dir, set_desktop_dir, unset_desktop_dir),
        (document_dir, set_document_dir, unset_document_dir),
        (download_dir, set_download_dir, unset_download_dir),
        (executable_dir, set_executable_dir, unset_executable_dir),
        (font_dir, set_font_dir, unset_font_dir),
        (home_dir, set_home_dir, unset_home_dir),
        (picture_dir, set_picture_dir, unset_picture_dir),
        (public_dir, set_public_dir, unset_public_dir),
        (runtime_dir, set_runtime_dir, unset_runtime_dir),
        (template_dir, set_template_dir, unset_template_dir),
        (video_dir, set_video_dir, unset_video_dir),
    );
}
