use reverse_bench::colors::*;
use reverse_bench::rc::{reverse_rc_tail, Link, Node};
use std::rc::Rc;

/// Traverses and prints a list without cloning or altering any reference counts.
fn print_list_ref(name: &str, head: &Link<i32>) {
    print!("  {BOLD}{name}:{RESET} ");
    let mut cur = head.as_ref();
    let mut first = true;
    while let Some(rc_node) = cur {
        if !first {
            print!(" -> ");
        }
        first = false;
        print!(
            "Node({BOLD}{}{RESET}, addr: {YELLOW}{:p}{RESET}, RC: {GREEN}{}{RESET})",
            rc_node.val,
            Rc::as_ptr(rc_node),
            Rc::strong_count(rc_node)
        );
        cur = rc_node.next.as_ref();
    }
    if first {
        print!("(empty)");
    }
    println!();
}

// =========================================================================
// Preset 1: 3-Way Sharing (RC = 3 on Node 3)
// =========================================================================
fn preset_1_three_way() {
    println!(
        "{BOLD}{CYAN}======================================================================{RESET}"
    );
    println!(
        "{BOLD}{CYAN} Preset 1: 3-Way Sharing (RC = 3 on Node 3)                          {RESET}"
    );
    println!("{DIM} list1 (1->2), list2 (11->22), and list3 (13->23) converge on Node 3 {RESET}");
    println!("{DIM} Expected: Nodes 1 & 2 reuse in-place. Nodes 3 & 4 trigger COW.       {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let n4 = Rc::new(Node { val: 4, next: None });
    let n3 = Rc::new(Node {
        val: 3,
        next: Some(n4),
    });

    let list1 = Some(Rc::new(Node {
        val: 1,
        next: Some(Rc::new(Node {
            val: 2,
            next: Some(n3.clone()),
        })),
    }));
    let list2 = Some(Rc::new(Node {
        val: 11,
        next: Some(Rc::new(Node {
            val: 22,
            next: Some(n3.clone()),
        })),
    }));
    let list3 = Some(Rc::new(Node {
        val: 13,
        next: Some(Rc::new(Node {
            val: 23,
            next: Some(n3),
        })), // n3 moved into list3
    }));

    let orig_addr_1 = Rc::as_ptr(list1.as_ref().unwrap());
    let orig_addr_2 = Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap());
    let orig_addr_3 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );
    let orig_addr_4 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("list2", &list2);
    print_list_ref("list3", &list3);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("list2   ", &list2);
    print_list_ref("list3   ", &list3);

    println!("\n{BOLD}Address Verification:{RESET}");
    let r4 = reversed.as_ref().unwrap();
    let r3 = r4.next.as_ref().unwrap();
    let r2 = r3.next.as_ref().unwrap();
    let r1 = r2.next.as_ref().unwrap();

    let new_addr_4 = Rc::as_ptr(r4);
    let new_addr_3 = Rc::as_ptr(r3);
    let new_addr_2 = Rc::as_ptr(r2);
    let new_addr_1 = Rc::as_ptr(r1);

    println!(
        "  Node 1: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_1,
        new_addr_1,
        if orig_addr_1 == new_addr_1 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 2: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_2,
        new_addr_2,
        if orig_addr_2 == new_addr_2 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 3: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_3,
        new_addr_3,
        if orig_addr_3 == new_addr_3 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 4: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_4,
        new_addr_4,
        if orig_addr_4 == new_addr_4 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );

    drop(reversed);
    drop(list2);
    drop(list3);
}

// =========================================================================
// Preset 2: Head Shared (RC = 2 on Node 1)
// =========================================================================
fn preset_2_root_shared() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 2: Head Shared (RC = 2 on Node 1)                             {RESET}"
    );
    println!("{DIM} Persistent clone on list head -> Full COW cascade                    {RESET}");
    println!("{DIM} Expected: All nodes trigger COW because head is shared.              {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let list1 = Some(Rc::new(Node {
        val: 1,
        next: Some(Rc::new(Node {
            val: 2,
            next: Some(Rc::new(Node { val: 3, next: None })),
        })),
    }));
    let clone = list1.clone();

    let orig_addr_1 = Rc::as_ptr(list1.as_ref().unwrap());
    let orig_addr_2 = Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap());
    let orig_addr_3 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("clone", &clone);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("clone   ", &clone);

    println!("\n{BOLD}Address Verification:{RESET}");
    let r3 = reversed.as_ref().unwrap();
    let r2 = r3.next.as_ref().unwrap();
    let r1 = r2.next.as_ref().unwrap();

    let new_addr_3 = Rc::as_ptr(r3);
    let new_addr_2 = Rc::as_ptr(r2);
    let new_addr_1 = Rc::as_ptr(r1);

    println!(
        "  Node 1: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_1,
        new_addr_1,
        if orig_addr_1 == new_addr_1 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 2: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_2,
        new_addr_2,
        if orig_addr_2 == new_addr_2 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 3: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_3,
        new_addr_3,
        if orig_addr_3 == new_addr_3 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );

    drop(reversed);
    drop(clone);
}

// =========================================================================
// Preset 3: Classic Shared Tail (2-Way)
// =========================================================================
fn preset_3_shared_tail() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 3: Classic Shared Tail (2-Way)                                {RESET}"
    );
    println!("{DIM} list1 (1->2->3) and list2 (11->2->3)                                {RESET}");
    println!("{DIM} Expected: Node 1 reuses in-place (RC=1). Nodes 2 & 3 trigger COW.    {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let tail = Some(Rc::new(Node {
        val: 2,
        next: Some(Rc::new(Node { val: 3, next: None })),
    }));
    let list1 = Some(Rc::new(Node {
        val: 1,
        next: tail.clone(),
    }));
    let list2 = Some(Rc::new(Node {
        val: 11,
        next: tail,
    })); // tail moved into list2

    let orig_addr_1 = Rc::as_ptr(list1.as_ref().unwrap());
    let orig_addr_2 = Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap());
    let orig_addr_3 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("list2", &list2);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("list2   ", &list2);

    println!("\n{BOLD}Address Verification:{RESET}");
    let r3 = reversed.as_ref().unwrap();
    let r2 = r3.next.as_ref().unwrap();
    let r1 = r2.next.as_ref().unwrap();

    let new_addr_3 = Rc::as_ptr(r3);
    let new_addr_2 = Rc::as_ptr(r2);
    let new_addr_1 = Rc::as_ptr(r1);

    println!(
        "  Node 1: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_1,
        new_addr_1,
        if orig_addr_1 == new_addr_1 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 2: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_2,
        new_addr_2,
        if orig_addr_2 == new_addr_2 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 3: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_3,
        new_addr_3,
        if orig_addr_3 == new_addr_3 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );

    drop(reversed);
    drop(list2);
}

// =========================================================================
// Preset 4: 100% Unique List (0 Allocations)
// =========================================================================
fn preset_4_all_unique() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 4: 100% Unique List (FIP In-Place)                            {RESET}"
    );
    println!("{DIM} All nodes have RC = 1 -> 0 allocations                               {RESET}");
    println!("{DIM} Expected: 100% in-place mutation, all memory addresses preserved.    {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let list1 = Some(Rc::new(Node {
        val: 1,
        next: Some(Rc::new(Node {
            val: 2,
            next: Some(Rc::new(Node {
                val: 3,
                next: Some(Rc::new(Node { val: 4, next: None })),
            })),
        })),
    }));

    let orig_addr_1 = Rc::as_ptr(list1.as_ref().unwrap());
    let orig_addr_2 = Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap());
    let orig_addr_3 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );
    let orig_addr_4 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);

    println!("\n{BOLD}Address Verification:{RESET}");
    let r4 = reversed.as_ref().unwrap();
    let r3 = r4.next.as_ref().unwrap();
    let r2 = r3.next.as_ref().unwrap();
    let r1 = r2.next.as_ref().unwrap();

    let new_addr_4 = Rc::as_ptr(r4);
    let new_addr_3 = Rc::as_ptr(r3);
    let new_addr_2 = Rc::as_ptr(r2);
    let new_addr_1 = Rc::as_ptr(r1);

    println!(
        "  Node 1: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_1,
        new_addr_1,
        if orig_addr_1 == new_addr_1 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 2: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_2,
        new_addr_2,
        if orig_addr_2 == new_addr_2 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 3: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_3,
        new_addr_3,
        if orig_addr_3 == new_addr_3 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 4: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_4,
        new_addr_4,
        if orig_addr_4 == new_addr_4 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );

    drop(reversed);
}

// =========================================================================
// Preset 5: Middle Shared (External Handle)
// =========================================================================
fn preset_5_middle_shared() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 5: Middle Shared (External Handle)                            {RESET}"
    );
    println!("{DIM} Only Node 2 is held externally                                       {RESET}");
    println!("{DIM} Expected: Node 1 reuses in-place. Nodes 2, 3, 4 trigger COW.         {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let n4 = Rc::new(Node { val: 4, next: None });
    let n3 = Rc::new(Node {
        val: 3,
        next: Some(n4),
    });
    let n2 = Rc::new(Node {
        val: 2,
        next: Some(n3),
    });

    let list1 = Some(Rc::new(Node {
        val: 1,
        next: Some(n2.clone()),
    }));
    let handle = Some(n2); // n2 moved into handle

    let orig_addr_1 = Rc::as_ptr(list1.as_ref().unwrap());
    let orig_addr_2 = Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap());
    let orig_addr_3 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );
    let orig_addr_4 = Rc::as_ptr(
        list1
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap()
            .next
            .as_ref()
            .unwrap(),
    );

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1 ", &list1);
    print_list_ref("handle", &handle);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("handle  ", &handle);

    println!("\n{BOLD}Address Verification:{RESET}");
    let r4 = reversed.as_ref().unwrap();
    let r3 = r4.next.as_ref().unwrap();
    let r2 = r3.next.as_ref().unwrap();
    let r1 = r2.next.as_ref().unwrap();

    let new_addr_4 = Rc::as_ptr(r4);
    let new_addr_3 = Rc::as_ptr(r3);
    let new_addr_2 = Rc::as_ptr(r2);
    let new_addr_1 = Rc::as_ptr(r1);

    println!(
        "  Node 1: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_1,
        new_addr_1,
        if orig_addr_1 == new_addr_1 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{RED}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 2: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_2,
        new_addr_2,
        if orig_addr_2 == new_addr_2 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 3: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_3,
        new_addr_3,
        if orig_addr_3 == new_addr_3 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );
    println!(
        "  Node 4: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {}",
        orig_addr_4,
        new_addr_4,
        if orig_addr_4 == new_addr_4 {
            format!("{BOLD}{GREEN}REUSED IN-PLACE!{RESET}")
        } else {
            format!("{BOLD}{YELLOW}NEW via COW{RESET}")
        }
    );

    drop(reversed);
    drop(handle);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let filter = args.get(1).map(|s| s.as_str()).unwrap_or("all");

    match filter {
        "1" | "three-way" => preset_1_three_way(),
        "2" | "root-shared" => preset_2_root_shared(),
        "3" | "shared-tail" => preset_3_shared_tail(),
        "4" | "all-unique" => preset_4_all_unique(),
        "5" | "middle-shared" => preset_5_middle_shared(),
        "all" | _ => {
            preset_1_three_way();
            preset_2_root_shared();
            preset_3_shared_tail();
            preset_4_all_unique();
            preset_5_middle_shared();
        }
    }

    println!("\n{BOLD}{GREEN}=== All Verifications Finished ==={RESET}");
}
