-- Prove2me | Theorems.Thm_mme_exact_step_six_matrix_weight_rate
-- name    : mme_exact_step_six_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:22:20.799838+00:00
-- url     : https://prove2.me/theorems/29557005-8639-4ac5-848a-e203b07a9ea5
-- title:
--   Exact-step matrix weights retain explicit repair and rounding losses
-- statement:
--   A selected-count lower bound at least twice the repair budget guarantees surviving copies. The six-fold parent matrix weight includes six times log selected count minus the power-of-eight repair cost and log-two rounding allowance. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_exact_step_six_matrix_weight_log_rate
import Theorems.Thm_mme_exact_step_positive_copies_log_lower_bound
open MME MME.ProfiledCW
open scoped BigOperators
universe u

theorem mme_exact_step_six_matrix_weight_rate
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
        Real.log 2) + rate) ≤ ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by sorry
