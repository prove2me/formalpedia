-- Prove2me | solution 1 for RademacherSymmetrization.sum_exp_signed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:57.271583+00:00
-- url     : https://prove2.me/submissions/73b683da-5266-4cfe-9a39-7a68d17aff1a

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

open RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}











/-! ### The product measure -/





/-! ### Step 1: introducing the ghost sample -/



/-! ### Step 2: the swapping involution -/





/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/


/-! ### A Massart bound for the empirical Rademacher complexity of a finite class

To turn the symmetrization inequality into a concrete generalization bound we bound the
empirical Rademacher complexity of a finite class of uniformly bounded functions by the
Chernoff/moment generating function argument, exactly as in Massart's finite class
lemma.
-/









open RademacherSymmetrization in
omit [Fintype X] [DecidableEq X] in
theorem solution(v : Fin n → ℝ) (l : ℝ) :
    ∑ ε : Fin n → Bool, Real.exp (l * ∑ i, sgn ε i * v i)
      = ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i))) := by
  classical
  have hfac : ∀ ε : Fin n → Bool,
      Real.exp (l * ∑ i, sgn ε i * v i) = ∏ i, Real.exp (l * sgn ε i * v i) := by
    intro ε
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => Bool)
      (fun _ => (Finset.univ : Finset Bool))
      (fun i b => Real.exp (l * (if b then (1:ℝ) else -1) * v i))
  rw [Fintype.piFinset_univ] at h
  rw [Finset.sum_congr rfl (fun ε _ => hfac ε)]
  simp only [sgn]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  norm_num
