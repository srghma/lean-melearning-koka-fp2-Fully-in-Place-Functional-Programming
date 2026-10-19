import type { BaseStep } from './common';

export interface NoRcStep extends BaseStep {
  xs: number | null;
  acc: number | null;
  node: number | null;
  next: number | null;
  heap: (number | null)[];
  severed: { from: number; to: number | null } | null;
}
