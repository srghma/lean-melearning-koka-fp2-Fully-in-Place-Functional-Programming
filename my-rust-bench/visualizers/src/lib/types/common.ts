export type AlgoMode = 'while' | 'tail';

export interface CodeLine {
  num: number;
  text: string;
}

export interface RegisterItem {
  label: string;
  val: string;
  color: string;
}

export interface BaseStep {
  lineWhile: number;
  lineTail: number;
  title: string;
  desc: string;
  badge?: string;
  badgeType?: 'emerald' | 'amber' | 'purple' | 'slate';
}

export const toCodeLines = (src: string): CodeLine[] =>
  src
    .replace(/^\n+|\n+$/g, '')
    .split('\n')
    .map((text, idx) => ({ num: idx + 1, text }));
