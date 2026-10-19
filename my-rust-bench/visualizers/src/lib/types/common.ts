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
