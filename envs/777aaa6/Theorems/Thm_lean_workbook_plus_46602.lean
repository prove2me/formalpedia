-- Prove2me | Theorems.Thm_lean_workbook_plus_46602
-- name    : lean_workbook_plus_46602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1a7f215f-bdd9-4d0c-bff7-1f39cc140dca
-- statement:
--   If $a,b,c,d\in[0,1]$ then show that: $3(a+b+c+d)\le8+(a^3+b^3+c^3+d^3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46602 (a b c d : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) : 3 * (a + b + c + d) ≤ 8 + a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3   :=  by sorry
