-- Prove2me | solution 1 for lean_workbook_plus_7315
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:44:25.870518+00:00
-- url     : https://prove2.me/submissions/3bc882a7-5e64-49dc-814d-f3d545a66e44

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

def goldenNormPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let p := goldenNormPair n
    (2 * p.1 + p.2, p.1 + p.2)

theorem golden_norm_pair_properties (n : ℕ) :
    0 < (goldenNormPair n).1 ∧ 0 < (goldenNormPair n).2 ∧
      (goldenNormPair n).2 ≤ (goldenNormPair n).1 ∧
      (goldenNormPair n).1 ^ 2 + 1 =
        (goldenNormPair n).1 * (goldenNormPair n).2 + (goldenNormPair n).2 ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    let a := (goldenNormPair n).1
    let b := (goldenNormPair n).2
    change 0 < a ∧ 0 < b ∧ b ≤ a ∧ a ^ 2 + 1 = a * b + b ^ 2 at ih
    change 0 < 2 * a + b ∧ 0 < a + b ∧ a + b ≤ 2 * a + b ∧
      (2 * a + b) ^ 2 + 1 = (2 * a + b) * (a + b) + (a + b) ^ 2
    rcases ih with ⟨ha, hb, hba, he⟩
    exact ⟨by omega, by omega, by omega, by nlinarith [he]⟩

theorem golden_norm_pair_strict_mono : StrictMono fun n => (goldenNormPair n).1 := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := golden_norm_pair_properties n
  change (goldenNormPair n).1 < 2 * (goldenNormPair n).1 + (goldenNormPair n).2
  omega

theorem negative_golden_norm_positive_solutions_infinite :
    {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ b ≤ a ∧ a ^ 2 + 1 = a * b + b ^ 2}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => (goldenNormPair n).1)
  · exact golden_norm_pair_strict_mono.injective
  · intro n
    obtain ⟨ha, hb, hba, he⟩ := golden_norm_pair_properties n
    exact ⟨ha, (goldenNormPair n).2, hb, hba, he⟩

theorem solution (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b) :
    ∃ a b : ℕ, a ^ 2 - b ^ 2 = a * b - 1 := by
  obtain ⟨a, ha, b, hb, _, he⟩ := negative_golden_norm_positive_solutions_infinite.nonempty
  have hab : 0 < a * b := Nat.mul_pos ha hb
  exact ⟨a, b, by omega⟩
