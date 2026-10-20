use std::rc::Rc;

pub mod colors {
    pub const RESET: &str = "\x1b[0m";
    pub const BOLD: &str = "\x1b[1m";
    pub const DIM: &str = "\x1b[2m";
    pub const RED: &str = "\x1b[31m";
    pub const GREEN: &str = "\x1b[32m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const BLUE: &str = "\x1b[34m";
    pub const MAGENTA: &str = "\x1b[35m";
    pub const CYAN: &str = "\x1b[36m";
}

pub trait RcRef<T> {
    fn get_rc(&self) -> &Rc<T>;
}

impl<T> RcRef<T> for Rc<T> {
    #[inline(always)]
    fn get_rc(&self) -> &Rc<T> {
        self
    }
}

impl<T> RcRef<T> for &Rc<T> {
    #[inline(always)]
    fn get_rc(&self) -> &Rc<T> {
        self
    }
}

impl<T> RcRef<T> for &&Rc<T> {
    #[inline(always)]
    fn get_rc(&self) -> &Rc<T> {
        self
    }
}

#[inline(always)]
pub fn log_rc<T, R: RcRef<T>>(label: &str, rc: R) {
    #[cfg(feature = "rc-debug")]
    {
        use colors::*;
        let r = rc.get_rc();
        println!(
            "  {DIM}├─{RESET} [{CYAN}{label}{RESET}] {BOLD}strong{RESET}: {GREEN}{}{RESET}, {BOLD}weak{RESET}: {YELLOW}{}{RESET}",
            Rc::strong_count(r),
            Rc::weak_count(r)
        );
    }
    #[cfg(not(feature = "rc-debug"))]
    {
        let _ = (label, rc);
    }
}

#[macro_export]
macro_rules! dbg_rc {
    ($label:expr, $rc:expr) => {
        $crate::log_rc($label, &$rc);
    };
}

pub mod box_list;
pub mod box_to_box;
pub mod box_to_rc;
pub mod ownership_and_borrowing_four_by_four_matrix;
pub mod rc_list;
pub mod rc_to_box;
pub mod rc_to_rc;
