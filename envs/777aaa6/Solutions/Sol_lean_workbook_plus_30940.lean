-- Prove2me | solution 1 for lean_workbook_plus_30940
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:31:41.795943+00:00
-- url     : https://prove2.me/submissions/48297e4d-93f3-4d13-8299-0be9a9407821

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finite.Sum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

inductive StairPath : ℕ → Type
  | nil : StairPath 0
  | one {n : ℕ} : StairPath n → StairPath (n + 1)
  | two {n : ℕ} : StairPath n → StairPath (n + 2)

def StairPath.steps : {n : ℕ} → StairPath n → List ℕ
  | _, .nil => []
  | _, .one p => 1 :: p.steps
  | _, .two p => 2 :: p.steps

theorem StairPath.steps_sum {n : ℕ} (p : StairPath n) : p.steps.sum = n := by
  induction p with
  | nil => rfl
  | one p ih => rw [steps, List.sum_cons, ih, Nat.add_comm]
  | two p ih => rw [steps, List.sum_cons, ih, Nat.add_comm]

theorem StairPath.steps_allowed {n : ℕ} (p : StairPath n) :
    ∀ a ∈ p.steps, a = 1 ∨ a = 2 := by
  induction p with
  | nil => simp [steps]
  | one p ih => simpa [steps] using ih
  | two p ih => simpa [steps] using ih

private def stairZeroEquiv : StairPath 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .nil
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private def stairOneEquiv : StairPath 1 ≃ Unit where
  toFun _ := ()
  invFun _ := .one .nil
  left_inv p := by cases p with | one q => cases q; rfl
  right_inv p := by cases p; rfl

private def stairSplitEquiv (n : ℕ) :
    StairPath (n + 2) ≃ StairPath (n + 1) ⊕ StairPath n where
  toFun p := match p with
    | .one q => Sum.inl q
    | .two q => Sum.inr q
  invFun p := match p with
    | .inl q => .one q
    | .inr q => .two q
  left_inv p := by cases p <;> rfl
  right_inv p := by cases p <;> rfl

instance (n : ℕ) : Finite (StairPath n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact Finite.of_equiv Unit stairZeroEquiv.symm
  | one => exact Finite.of_equiv Unit stairOneEquiv.symm
  | more n ih0 ih1 =>
    letI : Finite (StairPath n) := ih0
    letI : Finite (StairPath (n + 1)) := ih1
    exact Finite.of_equiv (StairPath (n + 1) ⊕ StairPath n) (stairSplitEquiv n).symm

theorem staircase_count_zero : Nat.card (StairPath 0) = 1 := by
  simpa using Nat.card_congr stairZeroEquiv

theorem staircase_count_one : Nat.card (StairPath 1) = 1 := by
  simpa using Nat.card_congr stairOneEquiv

theorem staircase_count_recurrence (n : ℕ) :
    Nat.card (StairPath (n + 2)) =
      Nat.card (StairPath (n + 1)) + Nat.card (StairPath n) := by
  rw [Nat.card_congr (stairSplitEquiv n), Nat.card_sum]

theorem staircase_count_fibonacci (n : ℕ) :
    Nat.card (StairPath n) = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using staircase_count_zero
  | one => simpa using staircase_count_one
  | more n ih0 ih1 =>
    rw [staircase_count_recurrence, ih0, ih1]
    exact (Nat.add_comm _ _).trans (Nat.fib_add_two (n := n + 1)).symm

theorem solution (n : ℕ) :
    ∃ F : ℕ → ℕ, F 0 = 1 ∧ F 1 = 2 ∧ F (n + 2) = F (n + 1) + F n := by
  refine ⟨fun k => Nat.card (StairPath (k + 1)), ?_, ?_, ?_⟩
  · simpa using staircase_count_one
  · change Nat.card (StairPath 2) = 2
    rw [staircase_count_fibonacci]
    norm_num [Nat.fib_add_two]
  · change Nat.card (StairPath (n + 2 + 1)) =
      Nat.card (StairPath (n + 1 + 1)) + Nat.card (StairPath (n + 1))
    exact staircase_count_recurrence (n + 1)
