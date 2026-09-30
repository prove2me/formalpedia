-- Prove2me | solution 1 for lean_workbook_plus_33515
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:53.537912+00:00
-- url     : https://prove2.me/submissions/72d73c0a-8b1b-4aab-9630-e85a8be0d719

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private noncomputable def reciprocalSeq : ℕ → ℝ
  | 0 => 1
  | n + 1 => reciprocalSeq n + 1 / reciprocalSeq n

theorem solution : ¬ (∀ (x : ℕ → ℝ), x 0 = 1 →
    (∀ n, x (n + 1) = x n + 1 / x n) → 12 ≤ x 15 ∧ x 15 ≤ 15) := by
  have hb : ∀ n : ℕ,
      1 ≤ reciprocalSeq n ∧ (reciprocalSeq n)^2 ≤ 1 + 3 * (n : ℝ) := by
    intro n
    induction n with
    | zero => norm_num [reciprocalSeq]
    | succ n ih =>
      obtain ⟨hlower, hsquare⟩ := ih
      have hp : 0 < reciprocalSeq n := by linarith
      have hi : 0 ≤ 1 / reciprocalSeq n := (one_div_pos.mpr hp).le
      have hi1 : 1 / reciprocalSeq n ≤ 1 :=
        (div_le_iff₀ hp).2 (by simpa using hlower)
      have hisq : (1 / reciprocalSeq n)^2 ≤ 1 := by
        nlinarith [mul_nonneg hi (sub_nonneg.mpr hi1)]
      have hcancel : reciprocalSeq n * (1 / reciprocalSeq n) = 1 := by
        field_simp [ne_of_gt hp]
      constructor
      · change 1 ≤ reciprocalSeq n + 1 / reciprocalSeq n
        linarith
      · change (reciprocalSeq n + 1 / reciprocalSeq n)^2 ≤ 1 + 3 * ((n + 1 : ℕ) : ℝ)
        push_cast
        nlinarith only [hsquare, hisq, hcancel]
  intro h
  have hclaimed := (h reciprocalSeq rfl (fun _ => rfl)).1
  have hsquare := (hb 15).2
  norm_num at hsquare
  nlinarith
