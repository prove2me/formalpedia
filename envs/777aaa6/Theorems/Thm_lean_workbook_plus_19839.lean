-- Prove2me | Theorems.Thm_lean_workbook_plus_19839
-- name    : lean_workbook_plus_19839
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3ff404f8-69ad-4c67-8a48-1f96e20941aa
-- statement:
--   prove that: $\frac{2}{3} \leq \frac{a(c-d)+3d}{b(d-c)+3c} \leq \frac{3}{2}$, where $a,b,c,d\in [2;3]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19839 (a b c d : ℝ) (ha : a ∈ Set.Icc 2 3) (hb : b ∈ Set.Icc 2 3) (hc : c ∈ Set.Icc 2 3) (hd : d ∈ Set.Icc 2 3) : (2 / 3 ≤ (a * (c - d) + 3 * d) / (b * (d - c) + 3 * c) ∧ (a * (c - d) + 3 * d) / (b * (d - c) + 3 * c) ≤ 3 / 2)   :=  by sorry
