-- Prove2me | solution 1 for InformationGeometry.klDiv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:17.858439+00:00
-- url     : https://prove2.me/submissions/8cd5f6a2-15d2-4db6-9d23-39c977f1b37e

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




















open InformationGeometry in
theorem solution(p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    0 ≤ klDiv p q := by
  have h_sum : ∑ i, p i * (1 - q i / p i) ≤
      ∑ i, p i * Real.log (p i / q i) := by
    gcongr with i
    · exact le_of_lt (hp i)
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (hq i) (hp i))
      rw [Real.log_div (ne_of_gt (hq i)) (ne_of_gt (hp i))] at hlog
      rw [Real.log_div (ne_of_gt (hp i)) (ne_of_gt (hq i))]
      linarith
  have hcancel : ∑ i, p i * (1 - q i / p i) = 0 := by
    have hterm : ∀ i, p i * (1 - q i / p i) = p i - q i := fun i => by
      field_simp [ne_of_gt (hp i)]
    simp only [hterm, Finset.sum_sub_distrib, hps, hqs, sub_self]
  rw [klDiv]
  linarith
