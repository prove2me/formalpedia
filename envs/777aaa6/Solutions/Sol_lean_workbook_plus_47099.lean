-- Prove2me | solution 1 for lean_workbook_plus_47099
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:53.449336+00:00
-- url     : https://prove2.me/submissions/95a4376b-be3f-4461-bcce-95db6d38e6a1

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) (f : ℕ → ℝ)
    (hf : f 0 = Real.sqrt 2 ∧ ∀ n, f (n + 1) = Real.sqrt (2 + f n)) :
    f n < f (n + 1) := by
  have hnonneg (m : ℕ) : 0 ≤ f m := by
    cases m with
    | zero => rw [hf.1]; exact Real.sqrt_nonneg 2
    | succ m => rw [hf.2]; exact Real.sqrt_nonneg _
  induction n with
  | zero =>
    rw [hf.2, hf.1]
    apply Real.sqrt_lt_sqrt (by norm_num)
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  | succ n ih =>
    calc
      f (n + 1) = Real.sqrt (2 + f n) := hf.2 n
      _ < Real.sqrt (2 + f (n + 1)) :=
        Real.sqrt_lt_sqrt (by linarith [hnonneg n]) (by linarith)
      _ = f (n + 1 + 1) := (hf.2 (n + 1)).symm
