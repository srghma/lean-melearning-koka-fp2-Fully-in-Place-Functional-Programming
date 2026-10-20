import { toCodeLines, type CodeLine } from '#lib/types/common';

export const BOX_TO_BOX_WHILE_CODE: CodeLine[] = toCodeLines(`pub fn reverse(mut self) -> Self {
    let mut acc = None;
    let mut xs = self.head.take();
    while let Some(mut node) = xs {
        let next = node.next.take();
        node.next = acc;
        acc = Some(node);
        xs = next;
    }
    List { head: acc }
}`);
export const BOX_TO_BOX_TAIL_CODE: CodeLine[] =
  toCodeLines(`fn reverse_acc<T>(xs: Link<T>, acc: Link<T>) -> Link<T> {
    match xs {
        Some(mut node) => {
            let next = node.next.take();
            node.next = acc;
            reverse_acc(next, Some(node))
        }
        None => acc,
    }
}`);
