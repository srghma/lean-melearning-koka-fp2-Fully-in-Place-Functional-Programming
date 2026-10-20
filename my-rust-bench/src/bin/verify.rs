use reverse_bench::box_to_rc::reverse_box_to_rc_tail;
use reverse_bench::colors::*;
use reverse_bench::rc_list::{Link, Node};
use reverse_bench::rc_to_box::reverse_rc_to_box_tail;
use reverse_bench::rc_to_rc::reverse_rc_to_rc_tail;
use std::collections::HashMap;
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

/// Verifies whether nodes in the reversed list were reused in-place or freshly allocated via COW.
fn verify_addresses(orig_nodes: &[(i32, *const Node<i32>)], reversed: &Link<i32>) {
    println!("\n{BOLD}Address Verification:{RESET}");
    let mut new_addrs: HashMap<i32, *const Node<i32>> = HashMap::new();
    let mut cur = reversed.as_ref();
    while let Some(rc_node) = cur {
        new_addrs.insert(rc_node.val, Rc::as_ptr(rc_node));
        cur = rc_node.next.as_ref();
    }

    for &(val, orig_addr) in orig_nodes {
        let new_addr = new_addrs.get(&val).copied().unwrap_or(std::ptr::null());
        let (status, color) = if orig_addr == new_addr {
            ("REUSED IN-PLACE!", GREEN)
        } else {
            ("NEW via COW", YELLOW)
        };
        println!(
            "  Node {val}: orig = {CYAN}{:p}{RESET}, new = {CYAN}{:p}{RESET} -> {BOLD}{color}{status}{RESET}",
            orig_addr, new_addr
        );
    }
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
    let orig_addr_4 = Rc::as_ptr(&n4);
    let n3 = Rc::new(Node {
        val: 3,
        next: Some(n4),
    });
    let orig_addr_3 = Rc::as_ptr(&n3);

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
        })),
    }));

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (3, orig_addr_3),
        (4, orig_addr_4),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("list2", &list2);
    print_list_ref("list3", &list3);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("list2   ", &list2);
    print_list_ref("list3   ", &list3);

    verify_addresses(&orig_nodes, &reversed);

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

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (
            3,
            Rc::as_ptr(
                list1
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap(),
            ),
        ),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("clone", &clone);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("clone   ", &clone);

    verify_addresses(&orig_nodes, &reversed);

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
    }));

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (
            3,
            Rc::as_ptr(
                list1
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap(),
            ),
        ),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);
    print_list_ref("list2", &list2);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("list2   ", &list2);

    verify_addresses(&orig_nodes, &reversed);

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

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (
            3,
            Rc::as_ptr(
                list1
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap(),
            ),
        ),
        (
            4,
            Rc::as_ptr(
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
            ),
        ),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1", &list1);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);

    verify_addresses(&orig_nodes, &reversed);

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
    let handle = Some(n2);

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (
            3,
            Rc::as_ptr(
                list1
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap(),
            ),
        ),
        (
            4,
            Rc::as_ptr(
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
            ),
        ),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1 ", &list1);
    print_list_ref("handle", &handle);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("handle  ", &handle);

    verify_addresses(&orig_nodes, &reversed);

    drop(reversed);
    drop(handle);
}

// =========================================================================
// Preset 6: Last Node Shared (RC = 2 on Tail)
// =========================================================================
fn preset_6_last_shared() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 6: Last Node Shared (RC = 2 on Tail)                          {RESET}"
    );
    println!("{DIM} Nodes 1, 2, 3 unique; only Node 4 is held externally                {RESET}");
    println!("{DIM} Expected: Nodes 1, 2, 3 reuse in-place. Node 4 triggers COW.        {RESET}");
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    let n4 = Rc::new(Node { val: 4, next: None });
    let orig_addr_4 = Rc::as_ptr(&n4);
    let handle = Some(n4.clone()); // handle keeps n4 alive (RC = 2)

    let list1 = Some(Rc::new(Node {
        val: 1,
        next: Some(Rc::new(Node {
            val: 2,
            next: Some(Rc::new(Node {
                val: 3,
                next: Some(n4), // n4 moved into list1
            })),
        })),
    }));

    let orig_nodes = [
        (1, Rc::as_ptr(list1.as_ref().unwrap())),
        (
            2,
            Rc::as_ptr(list1.as_ref().unwrap().next.as_ref().unwrap()),
        ),
        (
            3,
            Rc::as_ptr(
                list1
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap()
                    .next
                    .as_ref()
                    .unwrap(),
            ),
        ),
        (4, orig_addr_4),
    ];

    println!("{BOLD}Initial State:{RESET}");
    print_list_ref("list1 ", &list1);
    print_list_ref("handle", &handle);

    println!("\n{BOLD}{MAGENTA}--- Executing reverse_rc_to_rc_tail(list1) ---{RESET}");
    let reversed = reverse_rc_to_rc_tail(list1);

    println!("\n{BOLD}After Reverse:{RESET}");
    print_list_ref("reversed", &reversed);
    print_list_ref("handle  ", &handle);

    verify_addresses(&orig_nodes, &reversed);

    drop(reversed);
    drop(handle);
}

// =========================================================================
// Preset 7: Cross-Representation (Rc <-> Box)
// =========================================================================
fn preset_7_cross_repr() {
    println!("\n{BOLD}{CYAN}======================================================================{RESET}");
    println!(
        "{BOLD}{CYAN} Preset 6: Cross-Representation (Rc <-> Box)                          {RESET}"
    );
    println!(
        "{DIM} 1. reverse : List a -> List a {{Unique}} (Rc -> Box)                   {RESET}"
    );
    println!(
        "{DIM} 2. reverse : List a {{Unique}} -> List a (Box -> Rc)                   {RESET}"
    );
    println!("{BOLD}{CYAN}======================================================================{RESET}\n");

    println!("{BOLD}--- Case A: Unique Rc -> Box (try_unwrap avoids val clone) ---{RESET}");
    let rc_uniq = Some(Rc::new(Node {
        val: 10,
        next: Some(Rc::new(Node {
            val: 20,
            next: Some(Rc::new(Node {
                val: 30,
                next: None,
            })),
        })),
    }));
    print_list_ref("rc_uniq (before)", &rc_uniq);
    let boxed_from_uniq = reverse_rc_to_box_tail(rc_uniq);
    print!("  {BOLD}boxed_from_uniq:{RESET} ");
    let mut bcur = boxed_from_uniq.as_ref();
    while let Some(bnode) = bcur {
        print!("BoxNode({BOLD}{}{RESET}) -> ", bnode.val);
        bcur = bnode.next.as_ref();
    }
    println!("(empty)");

    println!("\n{BOLD}--- Case B: Shared Rc -> Box (COW clone of val) ---{RESET}");
    let rc_shared_orig = Some(Rc::new(Node {
        val: 100,
        next: Some(Rc::new(Node {
            val: 200,
            next: Some(Rc::new(Node {
                val: 300,
                next: None,
            })),
        })),
    }));
    let rc_shared_keep = rc_shared_orig.clone();
    print_list_ref("rc_shared_orig", &rc_shared_orig);
    let boxed_from_shared = reverse_rc_to_box_tail(rc_shared_orig);
    print!("  {BOLD}boxed_from_shared:{RESET} ");
    let mut bcur = boxed_from_shared.as_ref();
    while let Some(bnode) = bcur {
        print!("BoxNode({BOLD}{}{RESET}) -> ", bnode.val);
        bcur = bnode.next.as_ref();
    }
    println!("(empty)");
    print_list_ref("rc_shared_keep", &rc_shared_keep);

    println!("\n{BOLD}--- Case C: Box -> Rc reversal ---{RESET}");
    let rc_back = reverse_box_to_rc_tail(boxed_from_uniq);
    print_list_ref("rc_back", &rc_back);
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
        "6" | "last-shared" => preset_6_last_shared(),
        "7" | "cross" => preset_7_cross_repr(),
        _ => {
            preset_1_three_way();
            preset_2_root_shared();
            preset_3_shared_tail();
            preset_4_all_unique();
            preset_5_middle_shared();
            preset_6_last_shared();
            preset_7_cross_repr();
        }
    }

    println!("\n{BOLD}{GREEN}=== All Verifications Finished ==={RESET}");
}
