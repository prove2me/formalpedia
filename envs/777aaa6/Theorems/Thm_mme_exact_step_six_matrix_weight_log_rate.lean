-- Prove2me | Theorems.Thm_mme_exact_step_six_matrix_weight_log_rate
-- name    : mme_exact_step_six_matrix_weight_log_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:14:00.574835+00:00
-- url     : https://prove2.me/theorems/05833f67-4ac3-473b-bde7-edf773489ad1
-- title:
--   Exact steps add six times their logarithmic copy rate
-- statement:
--   A positive exact step combines a certified logarithmic copy rate with a child matrix-family weight rate. The six-fold parent tensor attains their summed exponent with positive output multiplicity. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_six_repeated_matrix_family_weight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
open MME MME.ProfiledCW
open scoped BigOperators
universe u

theorem mme_exact_step_six_matrix_weight_log_rate
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) (hp : 0 < E.copies)
    (parentRate : ℝ) (hlog : parentRate ≤ Real.log E.copies)
    {q : ℕ} (a b c : Fin q → ℕ) (hq : 0 < q) (tau rate : ℝ)
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization (tensor K E.output)))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization (tensor K P)) ∧
      Real.exp (6 * parentRate + rate) ≤ ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by sorry
