import type { BaseStep } from './common';

export interface RcArrow {
  from: string;
  to: string;
  type: 'forward' | 'shared-root' | 'severed' | 'backward' | 'cow-backward';
  label?: string;
  color?: string;
}

export interface NodeMeta {
  id: string;
  addr: string;
  val: number;
  label: string;
  x: number;
  y: number;
  tag: string;
}

export interface RcStep extends BaseStep {
  xs: string;
  acc: string;
  rc_node: string | null;
  getMut: string | null;
  nodeRCs: Record<string, number>;
  arrows: RcArrow[];
  visibleNodes: string[];
}

export interface RootDef {
  name: string;
  targetAddr: string;
  color: string;
}

export interface PresetNodeDef {
  id: string;
  addr: string;
  val: number;
  label: string;
  next: string | null; // target addr or null
  x: number;
  y: number;
  tag: string;
}

export interface RcPresetConfig {
  id: string;
  name: string;
  shortDesc: string;
  longDesc: string;
  activeRoot: string;
  roots: RootDef[];
  nodes: PresetNodeDef[];
  canvasWidth: number;
  canvasHeight: number;
}
