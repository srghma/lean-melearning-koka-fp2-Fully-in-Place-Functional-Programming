import { toCodeLines, type CodeLine } from '#lib/types/common';

export const BOX_TO_RC_WHILE_CODE: CodeLine[] =
  toCodeLines(`pub fn reverse_box_to_rc_while<T>(mut xs: BoxLink<T>) -> RcLink<T> {
    let mut acc = None;
    while let Some(mut box_node) = xs {
        xs = box_node.next.take();
        acc = Some(Rc::new(RcNode {
            val: box_node.val,
            next: acc,
        }));
    }
    acc
}`);
export const BOX_TO_RC_TAIL_CODE: CodeLine[] =
  toCodeLines(`fn reverse_box_to_rc_tail_acc<T>(xs: BoxLink<T>, acc: RcLink<T>) -> RcLink<T> {
    match xs {
        Some(mut box_node) => {
            let next = box_node.next.take();
            let new_rc = Rc::new(RcNode {
                val: box_node.val,
                next: acc,
            });
            reverse_box_to_rc_tail_acc(next, Some(new_rc))
        }
        None => acc,
    }
}`);
