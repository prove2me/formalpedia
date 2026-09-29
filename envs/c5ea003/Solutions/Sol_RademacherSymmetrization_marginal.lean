-- Prove2me | solution 1 for RademacherSymmetrization.marginal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:14.567172+00:00
-- url     : https://prove2.me/submissions/b3502170-bc4e-4950-bf25-a74d2accf899

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
omit [DecidableEq X] in
theorem solution{p : X → ℝ} (hp1 : ∑ x, p x = 1) (i : Fin n) (g : X → ℝ) :
    ∑ S : Fin n → X, wt p S * g (S i) = ∑ x, p x * g x := by
  classical
  have hfac : ∀ S : Fin n → X, wt p S * g (S i)
      = ∏ j, (if j = i then p (S j) * g (S j) else p (S j)) := by
    intro S
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
    unfold wt
    rw [← Finset.mul_prod_erase _ (fun j => p (S j)) (Finset.mem_univ i)]
    have hrest : ∀ j ∈ (Finset.univ.erase i),
        (if j = i then p (S j) * g (S j) else p (S j)) = p (S j) := by
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [Finset.prod_congr rfl hrest]
    ring
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => X)
      (fun _ => (Finset.univ : Finset X))
      (fun j x => if j = i then p x * g x else p x)
  rw [Fintype.piFinset_univ] at h
  rw [Finset.sum_congr rfl fun S _ => hfac S, ← h]
  have hterm : ∀ i₁ : Fin n, (∑ x, if i₁ = i then p x * g x else p x)
      = if i₁ = i then (∑ x, p x * g x) else 1 := by
    intro i₁
    by_cases hi : i₁ = i
    · simp [hi]
    · simp [hi, hp1]
  rw [Finset.prod_congr rfl fun i₁ _ => hterm i₁,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
  have hrest : ∀ j ∈ (Finset.univ.erase i),
      (if j = i then (∑ x, p x * g x) else (1:ℝ)) = 1 := by
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one]
