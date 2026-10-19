import type { CodeLine } from '#lib/types/common';

export const RC_WHILE_CODE: CodeLine[] = [
  { num: 1, text: 'pub fn reverse<T: Clone>(mut xs: Link<T>) -> Link<T> {' },
  { num: 2, text: '    let mut acc = None;' },
  { num: 3, text: '    while let Some(mut rc_node) = xs {' },
  { num: 4, text: '        match Rc::get_mut(&mut rc_node) {' },
  { num: 5, text: '            Some(node) => { // RC == 1: IN-PLACE' },
  { num: 6, text: '                xs = node.next.take();' },
  { num: 7, text: '                node.next = acc;' },
  { num: 8, text: '                acc = Some(rc_node); // Reuse block!' },
  { num: 9, text: '            }' },
  { num: 10, text: '            None => { // RC > 1: COPY-ON-WRITE' },
  { num: 11, text: '                xs = rc_node.next.clone();' },
  { num: 12, text: '                acc = Some(Rc::new(Node {' },
  { num: 13, text: '                    val: rc_node.val.clone(),' },
  { num: 14, text: '                    next: acc,' },
  { num: 15, text: '                }));' },
  { num: 16, text: '            }' },
  { num: 17, text: '        }' },
  { num: 18, text: '    }' },
  { num: 19, text: '    acc' },
  { num: 20, text: '}' }
];

export const RC_TAIL_CODE: CodeLine[] = [
  { num: 1, text: 'fn reverse_rc_tail_acc<T: Clone>(xs: Link<T>, acc: Link<T>) -> Link<T> {' },
  { num: 2, text: '    match xs {' },
  { num: 3, text: '        Some(mut rc_node) => match Rc::get_mut(&mut rc_node) {' },
  { num: 4, text: '            Some(node) => { // UNIQUE: IN-PLACE' },
  { num: 5, text: '                let next = node.next.take();' },
  { num: 6, text: '                node.next = acc;' },
  { num: 7, text: '                reverse_rc_tail_acc(next, Some(rc_node))' },
  { num: 8, text: '            }' },
  { num: 9, text: '            None => { // SHARED: COPY-ON-WRITE' },
  { num: 10, text: '                let next = rc_node.next.clone();' },
  { num: 11, text: '                let val = rc_node.val.clone();' },
  { num: 12, text: '                drop(rc_node); // Critical for TCO' },
  { num: 13, text: '                let new_node = Rc::new(Node { val, next: acc });' },
  { num: 14, text: '                reverse_rc_tail_acc(next, Some(new_node))' },
  { num: 15, text: '            }' },
  { num: 16, text: '        },' },
  { num: 17, text: '        None => acc,' },
  { num: 18, text: '    }' },
  { num: 19, text: '}' }
];
