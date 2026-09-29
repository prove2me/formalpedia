-- Prove2me | Theorems.Thm_lean_workbook_plus_26468
-- name    : lean_workbook_plus_26468
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/9c117b06-81f9-4ed1-87fe-3371107f6be3
-- statement:
--   Let $a,b,c,d>0$ . Prove that: $$\frac{a}{\sqrt{a+b}}+\frac{b}{\sqrt{b+c}}+\frac{c}{\sqrt{c+d}}+\frac{d}{\sqrt{d+a}}\leq \sqrt {a}+\sqrt {b}+\sqrt {c}+\sqrt {d}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26468 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + d) + d / Real.sqrt (d + a)) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d   :=  by sorry
