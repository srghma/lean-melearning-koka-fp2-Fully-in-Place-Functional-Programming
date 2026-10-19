use easybench::bench_env;
use reverse_bench::colors::*;
use reverse_bench::no_rc::List;
use reverse_bench::rc::{reverse_rc_tail, reverse_rc_while, RcList};

fn main() {
    let sizes = [100, 1_000, 10_000];

    // =========================================================================
    // SECTION 1: No-RC (Boxed List & Vec) Benchmarks
    // =========================================================================
    println!("{BOLD}{CYAN}============================================================{RESET}");
    println!("{BOLD}{CYAN} 1. NO-RC BENCHMARKS (Boxed Singly-Linked List vs Vec)     {RESET}");
    println!("{BOLD}{CYAN}============================================================{RESET}");

    for &n in &sizes {
        println!("\n{BOLD}=== List Size: {YELLOW}{n}{RESET}{BOLD} ==={RESET}");
        let list: List<i32> = List::from_iter(0..n);
        let vec: Vec<i32> = (0..n).collect();

        let rec_stat = bench_env(list.clone(), |l| {
            let owned = std::mem::take(l);
            *l = owned.reverse_rec();
            l.head.as_ref().map(|node| node.val)
        });

        let iter_stat = bench_env(list.clone(), |l| {
            let owned = std::mem::take(l);
            *l = owned.reverse_iter();
            l.head.as_ref().map(|node| node.val)
        });

        let vec_stat = bench_env(vec.clone(), |v| {
            v.reverse();
            v.first().copied()
        });

        println!("  {CYAN}tail-rec (inlined){RESET}   : {rec_stat}");
        println!("  {CYAN}iterative (while){RESET}    : {iter_stat}");
        println!("  {GREEN}vec (slice::reverse){RESET} : {vec_stat}");
    }

    // =========================================================================
    // SECTION 2: RC (Reference Counted List) Benchmarks
    // =========================================================================
    println!(
        "\n{BOLD}{MAGENTA}============================================================{RESET}"
    );
    println!("{BOLD}{MAGENTA} 2. RC BENCHMARKS: 100% Unique vs 100% Shared (Pure COW)    {RESET}");
    println!("{BOLD}{MAGENTA}============================================================{RESET}");

    for &n in &sizes {
        println!("\n{BOLD}--- Size: {YELLOW}{n}{RESET}{BOLD} ---{RESET}");

        // Scenario A: 100% Unique list (every node has RC == 1)
        let unique_list: RcList<i32> = RcList::from_iter(0..n);

        let unique_while = bench_env(unique_list.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_while(owned);
            l.head.as_ref().map(|node| node.val)
        });

        let unique_tail = bench_env(unique_list.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_tail(owned);
            l.head.as_ref().map(|node| node.val)
        });

        println!("  {GREEN}Unique (In-Place) While   {RESET}: {unique_while}");
        println!("  {GREEN}Unique (In-Place) Tail-Rec{RESET}: {unique_tail}");

        // Scenario B: 100% Shared list
        // Keep root alive and clone its head on each iteration so RC >= 2 is preserved
        let shared_list_root = RcList::from_iter(0..n);
        let _keep_alive = shared_list_root.clone();

        let cow_while = bench_env((), |_| {
            let owned = _keep_alive.head.clone();
            let reversed = reverse_rc_while(owned);
            reversed.as_ref().map(|node| node.val)
        });

        let cow_tail = bench_env((), |_| {
            let owned = _keep_alive.head.clone();
            let reversed = reverse_rc_tail(owned);
            reversed.as_ref().map(|node| node.val)
        });

        println!("  {YELLOW}Shared (COW Malloc) While {RESET}: {cow_while}");
        println!("  {YELLOW}Shared (COW Malloc) Tail  {RESET}: {cow_tail}");

        drop(_keep_alive);
        drop(shared_list_root);
        drop(unique_list);
    }
}
