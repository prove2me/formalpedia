-- Prove2me | solution 1 for RademacherSymmetrization.symmetrized_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:15:54.605406+00:00
-- url     : https://prove2.me/submissions/baddbae6-a290-43e4-b173-dd85458623fd

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


lemma sgn_not (ε : Fin n → Bool) (i : Fin n) : sgn (fun j => !(ε j)) i = -sgn ε i := by
  simp only [sgn]
  rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]









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
theorem solution(F : Finset (X → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool)
    (q : (Fin n → X) × (Fin n → X)) :
    F.sup' hne (fun f => (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i)))
      ≤ maxCorr F hne ε q.2 + maxCorr F hne (fun j => !(ε j)) q.1 := by
  refine Finset.sup'_le _ _ fun f hf => ?_
  have hsplit : (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i))
      = corr ε q.2 f + corr (fun j => !(ε j)) q.1 f := by
    unfold corr
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sgn_not]
    ring
  rw [hsplit]
  exact add_le_add (Finset.le_sup' (corr ε q.2) hf)
    (Finset.le_sup' (corr (fun j => !(ε j)) q.1) hf)
