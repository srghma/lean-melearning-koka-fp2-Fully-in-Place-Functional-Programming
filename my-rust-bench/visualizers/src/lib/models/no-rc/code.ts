import type { CodeLine } from '#lib/types/common';

export const NO_RC_WHILE_CODE: CodeLine[] = [
  { num: 1, text: 'pub fn reverse(mut self) -> Self {' },
  { num: 2, text: '    let mut acc = None;' },
  { num: 3, text: '    let mut xs = self.head.take();' },
  { num: 4, text: '    while let Some(mut node) = xs {' },
  { num: 5, text: '        let next = node.next.take();' },
  { num: 6, text: '        node.next = acc;' },
  { num: 7, text: '        acc = Some(node);' },
  { num: 8, text: '        xs = next;' },
  { num: 9, text: '    }' },
  { num: 10, text: '    List { head: acc }' },
  { num: 11, text: '}' }
];

export const NO_RC_TAIL_CODE: CodeLine[] = [
  { num: 1, text: 'fn reverse_acc<T>(xs: Link<T>, acc: Link<T>) -> Link<T> {' },
  { num: 2, text: '    match xs {' },
  { num: 3, text: '        Some(mut node) => {' },
  { num: 4, text: '            let next = node.next.take();' },
  { num: 5, text: '            node.next = acc;' },
  { num: 6, text: '            reverse_acc(next, Some(node))' },
  { num: 7, text: '        }' },
  { num: 8, text: '        None => acc,' },
  { num: 9, text: '    }' },
  { num: 10, text: '}' }
];
