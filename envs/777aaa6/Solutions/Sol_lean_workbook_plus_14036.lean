-- Prove2me | solution 1 for lean_workbook_plus_14036
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:07.653785+00:00
-- url     : https://prove2.me/submissions/efc034ef-da29-4dde-b603-fba57b1bb771

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1) (hc : c ∈ Set.Icc (1 / 2) 1) : a * b + b * c + c * a + 3 / 4 ≥ a + b + c := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
