import { toCodeLines, type CodeLine } from '#lib/types/common';

export const RC_TO_RC_WHILE_CODE: CodeLine[] =
  toCodeLines(`pub fn reverse<T: Clone>(mut xs: Link<T>) -> Link<T> {
    let mut acc = None;
    while let Some(mut rc_node) = xs {
        match Rc::get_mut(&mut rc_node) {
            Some(node) => { // RC == 1: IN-PLACE
                xs = node.next.take();
                node.next = acc;
                acc = Some(rc_node); // Reuse block!
            }
            None => { // RC > 1: COPY-ON-WRITE
                xs = rc_node.next.clone();
                acc = Some(Rc::new(Node {
                    val: rc_node.val.clone(),
                    next: acc,
                }));
            }
        }
    }
    acc
}`);
export const RC_TO_RC_TAIL_CODE: CodeLine[] =
  toCodeLines(`fn reverse_rc_tail_acc<T: Clone>(xs: Link<T>, acc: Link<T>) -> Link<T> {
    match xs {
        Some(mut rc_node) =>
            match Rc::get_mut(&mut rc_node) {
                Some(node) => { // UNIQUE: IN-PLACE
                    let next = node.next.take();
                    node.next = acc;
                    reverse_rc_tail_acc(next, Some(rc_node))
                }
                None => { // SHARED: COPY-ON-WRITE
                    let next = rc_node.next.clone();
                    let val = rc_node.val.clone();
                    drop(rc_node); // Critical for TCO
                    let new_node = Rc::new(Node { val, next: acc });
                    reverse_rc_tail_acc(next, Some(new_node))
                }
            },
        None => acc,
    }
}`);
