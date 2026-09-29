-- Prove2me | solution 1 for finite_contraction_fixedPoint_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T15:15:10.439991+00:00
-- url     : https://prove2.me/submissions/2dc8a732-4b68-46bc-81bc-c5acc64c05fd

-- Sol generated from Geometry/FiniteContraction.lean
import Mathlib

/-!
# A non-circular finite Banach fixed point theorem

A contraction on a nonempty finite metric space has a unique fixed point.

The proof is self-contained: it uses only finite minimization, basic metric-space
facts (`dist_eq_zero`, `dist_comm`), and ordered-ring arithmetic. It does **not**
rely on compactness, completeness, Cauchy sequences, Schauder/Brouwer, or any
existing fixed point theorem.
-/





theorem solution  {X : Type*} [MetricSpace X] [Fintype X] [Nonempty X]
  (f : X → X) {K : ℝ}
  (hK : K < 1)
  (hcontr : ∀ x y : X, dist (f x) (f y) ≤ K * dist x y) :
  ∃! x : X, f x = x := by
  -- By `Finset.exists_min_image` there is `a ∈ univ` minimizing δ, i.e. for all y, δ a ≤ δ y.
  obtain ⟨a, ha⟩ : ∃ a, ∀ y, dist a (f a) ≤ dist y (f y) := by
    simpa using Finset.exists_min_image Finset.univ ( fun x => dist x ( f x ) ) Finset.univ_nonempty;
  -- By `nonneg_eq_zero_of_le_mul_lt_one`, we have `dist a (f a) = 0`, so `f a = a`.
  have hfa : dist a (f a) = 0 := by
    contrapose! ha;
    exact ⟨ f a, by have := hcontr a ( f a ) ; nlinarith [ show 0 < dist a ( f a ) from lt_of_le_of_ne ( dist_nonneg ) ha.symm, show dist ( f a ) ( f ( f a ) ) < dist a ( f a ) from lt_of_le_of_lt ( hcontr a ( f a ) ) ( mul_lt_of_lt_one_left ( lt_of_le_of_ne ( dist_nonneg ) ha.symm ) hK ) ] ⟩
  have hfa_eq : f a = a := by
    exact dist_eq_zero.mp hfa ▸ rfl;
  refine' ⟨ a, hfa_eq, fun x hx => _ ⟩;
  exact dist_le_zero.mp ( by have := hcontr x a; norm_num [ hx, hfa_eq ] at this; nlinarith [ @dist_nonneg _ _ x a ] )
