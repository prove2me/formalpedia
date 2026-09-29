-- Prove2me | solution 1 for InformationGeometry.klDiv_le_fisher
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:17.401228+00:00
-- url     : https://prove2.me/submissions/79b47e10-3dc6-40ec-913f-8523f9fa8020

-- Sol generated from Bridges/InformationGeometry/FisherMetric.lean
import Mathlib
import Definitions.Def_Bridges_InformationGeometry_FisherMetric

/-!
# The Fisher metric on the finite statistical manifold

We model the open probability simplex on a finite type `ι`.  At a positive
probability vector `p`, tangent vectors are functions `ι → ℝ` (the Fisher form
restricts in particular to the usual zero-sum tangent hyperplane).

The file builds a chain from the score representation of Fisher information,
through all algebraic and positivity axioms of a real inner product, to a global
information-geometric comparison

`0 ≤ KL(p ‖ q) ≤ g_q(p - q, p - q)`.

Thus the local quadratic geometry is explicitly connected to statistical
relative entropy.  No analytic limiting assumptions are needed for this finite,
strictly positive model.
-/

noncomputable section

open Finset

open InformationGeometry

variable {ι : Type*} [Fintype ι]














/-- Pearson divergence is precisely Fisher squared distance at the displacement
`p - q`, based at `q`. -/
theorem chiSquared_eq_fisher (p q : ι → ℝ) :
    chiSquared p q = fisherForm q (p - q) (p - q) := by
  simp only [chiSquared, fisherForm, Pi.sub_apply, sq]






open InformationGeometry in
theorem solution(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    klDiv p q ≤ fisherForm q (p - q) (p - q) := by
  have h_log_le : ∑ i, p i * Real.log (p i / q i) ≤
      ∑ i, p i * (p i / q i - 1) := by
    gcongr with i
    · exact le_of_lt (hp i)
    · exact Real.log_le_sub_one_of_pos (div_pos (hp i) (hq i))
  have hrhs : ∑ i, p i * (p i / q i - 1) =
      fisherForm q (p - q) (p - q) := by
    rw [← chiSquared_eq_fisher]
    have hterm : ∀ i, p i * (p i / q i - 1) =
        (p i - q i) ^ 2 / q i + (p i - q i) := fun i => by
      field_simp [ne_of_gt (hq i)]
      ring
    simp only [chiSquared, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hps, hqs, sub_self, add_zero]
  rw [klDiv]
  exact h_log_le.trans_eq hrhs
