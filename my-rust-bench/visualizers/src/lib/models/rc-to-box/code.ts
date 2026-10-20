import { toCodeLines, type CodeLine } from '#lib/types/common';

export const RC_TO_BOX_WHILE_CODE: CodeLine[] =
  toCodeLines(`pub fn reverse_rc_to_box_while<T: Clone>(mut xs: RcLink<T>) -> BoxLink<T> {
    let mut acc = None;
    while let Some(rc_node) = xs {
        let (val, next) = match Rc::try_unwrap(rc_node) {
            Ok(mut unique_node) => {
                // Unique: 0 atomic updates, take next directly
                (unique_node.val, unique_node.next.take())
            }
            Err(shared_rc) => {
                // Shared: clone next pointer and clone val
                (shared_rc.val.clone(), shared_rc.next.clone())
            }
        };
        xs = next;
        acc = Some(Box::new(BoxNode { val, next: acc }));
    }
    acc
}`);
export const RC_TO_BOX_TAIL_CODE: CodeLine[] =
  toCodeLines(`fn reverse_rc_to_box_tail_acc<T: Clone>(xs: RcLink<T>, acc: BoxLink<T>) -> BoxLink<T> {
    match xs {
        Some(rc_node) => {
            let (val, next) = match Rc::try_unwrap(rc_node) {
                Ok(mut unique_node) => (unique_node.val, unique_node.next.take()),
                Err(shared_rc) => (shared_rc.val.clone(), shared_rc.next.clone()),
            };
            let new_box = Box::new(BoxNode { val, next: acc });
            reverse_rc_to_box_tail_acc(next, Some(new_box))
        }
        None => acc,
    }
}`);
