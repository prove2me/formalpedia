-- Prove2me | solution 1 for mme_exact_step_six_matrix_weight_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:16:45.429988+00:00
-- url     : https://prove2.me/submissions/17daa178-fc3b-4e59-9e6f-b30c7e1d028d

import Theorems.Thm_mme_six_repeated_matrix_family_weight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_recursive_profiled_CW_exact_step

open MME MME.ProfiledCW
open scoped BigOperators
universe u

/-- A positive exact step adds six times its certified logarithmic copy rate
to the matrix weight rate of its output tensor. -/
theorem solution
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
      Real.exp (6 * parentRate + rate) ≤ ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by
  obtain ⟨hrestrict, hrate⟩ := mme_six_repeated_matrix_family_weight a b c tau rate
    (mme_recursive_profiled_CW_exact_step (K := K) E) hchild hweight
  refine ⟨E.copies ^ 6 * q,
    (fun r => a (finProdFinEquiv.symm r).2),
    (fun r => b (finProdFinEquiv.symm r).2),
    (fun r => c (finProdFinEquiv.symm r).2),
    Nat.mul_pos (pow_pos hp _) hq, hrestrict, ?_⟩
  apply le_trans ?_ hrate
  have hpos : 0 < (E.copies : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ Real.exp (6 * Real.log (E.copies : ℝ) + rate) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = (E.copies : ℝ) ^ 6 * Real.exp rate := by
      rw [Real.exp_add]
      congr 1
      simpa using (Real.exp_nat_mul (Real.log (E.copies : ℝ)) 6).trans
        (congrArg (fun x : ℝ => x ^ 6) (Real.exp_log hpos))


#print axioms solution
