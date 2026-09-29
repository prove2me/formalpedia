-- Prove2me | solution 1 for mme_exact_step_six_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:24:47.116787+00:00
-- url     : https://prove2.me/submissions/4f6ad891-06ae-48c5-ac90-5de17e9341cc

import Theorems.Thm_mme_exact_step_six_matrix_weight_log_rate
import Theorems.Thm_mme_exact_step_positive_copies_log_lower_bound

open MME MME.ProfiledCW
open scoped BigOperators
universe u

/-- A surviving exact step amplifies a child matrix weight by six times the
parent log-copy rate, retaining the repair and integer-rounding allowances. -/
theorem solution
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) (B : ℝ) (hB : B ≤ E.count)
    (hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent ≤ B)
    {q : ℕ} (a b c : Fin q → ℕ) (hq : 0 < q) (tau rate : ℝ)
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization (tensor K E.output)))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization (tensor K P)) ∧
      Real.exp (6 * (Real.log B - (E.stage.repairExponent : ℝ) * Real.log 8 -
        Real.log 2) + rate) ≤ ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by
  obtain ⟨hp, hlog⟩ := mme_exact_step_positive_copies_log_lower_bound E hB hlarge
  exact mme_exact_step_six_matrix_weight_log_rate E hp _ hlog.le
    a b c hq tau rate hchild hweight


#print axioms solution
