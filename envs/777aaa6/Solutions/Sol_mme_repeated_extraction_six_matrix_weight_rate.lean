-- Prove2me | solution 1 for mme_repeated_extraction_six_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:38:05.083135+00:00
-- url     : https://prove2.me/submissions/19ba0cb7-e0fc-4323-b050-264d88b737b3

import Theorems.Thm_mme_six_repeated_matrix_family_weight
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MME
open scoped BigOperators
universe u

/-- A repeated extraction contributes six times its logarithmic copy bound
when composed with a matrix family in the symmetrized output. -/
theorem solution
    {K : Type u} [Field K] {p q : ℕ} {X Y : TensorObj K 3}
    (a b c : Fin q → ℕ) (hq : 0 < q) (tau parentRate rate : ℝ)
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hcopies : Real.exp parentRate ≤ (p : ℝ))
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization Y))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization X) ∧
      Real.exp (6 * parentRate + rate) ≤
        ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by
  obtain ⟨hrestrict, hrate⟩ :=
    mme_six_repeated_matrix_family_weight a b c tau rate hparent hchild hweight
  have hp : 0 < p := Nat.cast_pos.mp ((Real.exp_pos parentRate).trans_le hcopies)
  refine ⟨p ^ 6 * q,
    (fun r => a (finProdFinEquiv.symm r).2),
    (fun r => b (finProdFinEquiv.symm r).2),
    (fun r => c (finProdFinEquiv.symm r).2),
    Nat.mul_pos (pow_pos hp _) hq, hrestrict, ?_⟩
  apply le_trans ?_ hrate
  rw [Real.exp_add, show Real.exp (6 * parentRate) = (Real.exp parentRate) ^ 6 by
    simpa using Real.exp_nat_mul parentRate 6]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_pos parentRate).le hcopies 6) (Real.exp_pos rate).le


#print axioms solution
