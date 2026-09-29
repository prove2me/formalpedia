-- Prove2me | solution 1 for Catalog.Geometry.Peel.bodyLayer_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:21:58.175694+00:00
-- url     : https://prove2.me/submissions/aed5d656-2c03-4416-8afc-e8ce646462c2

-- Sol generated from Geometry/PeelDilationBodies.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
/-
# Cycle 3: universality of the matching family

The shell peeling of a Euclidean ball saturates the peeling bound, and the
`O(d)`-action on its layers exhibits the symmetry responsible for that
saturation.  A natural criticism is that this could be an artefact of the
ball: the ball is the most symmetric body there is, so of course it produces a
symmetric peeling.

This file removes that objection: the construction is *universal*.  For **any**
star-shaped body `K ⊆ ℝ^d` of finite measure the dilates
`c_k • K`, `c_k = (1 - k/N)^{1/d}`, peel `K` into `N` pieces of equal measure
`vol K / N` (`bodyPeel_gap`, `bodyLayer_volume`), and every layer is invariant
under the *entire* linear symmetry group of `K` (`bodyLayer_equivariant`).
Conversely, a dilation peeling all of whose layers have measure at most
`vol K / N` must be this one (`body_peel_rigidity`).  The ball family of the
previous file is the special case `K = B(0,1)`, where the symmetry group is
`O(d)`.

The upshot for the original question — a matching family of actions for the
peeling upper bound — is that the extremisers are parameterised by *all* pairs
`(K, G)` with `G` a group of linear symmetries of `K`: the dimension `d` fixes
the radial profile `(1 - k/N)^{1/d}`, and the body `K` is otherwise free.

## Lab notes

Cross-check in `d = 2` with `K` the unit square `[-1,1]^2` (`vol K = 4`) and
`N = 4`: dilation factors `1, √(3)/2, √(2)/2, 1/2, 0`, layer areas
`4·(1/4) = 1` each — identical factors to the disc case, as the theory
predicts: the factors depend only on `d` and `N`, never on `K`.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric Pointwise

/-! ## Volumes of dilates -/





/-! ## Star-shaped bodies and nested dilates -/



/-! ## The universal equal-volume dilation peeling -/














/-! ## Rigidity for arbitrary bodies -/





open Catalog.Geometry.Peel in
theorem solution(d N k : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (he : e '' K = K) :
    e '' bodyLayer d K N k = bodyLayer d K N k := by
  have himg : ∀ c : ℝ, e '' (c • K) = c • K := by
    intro c
    have hcomm : e '' (c • K) = c • (e '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_smul_set]
      constructor
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨c • z, ⟨z, hz, rfl⟩, by simp⟩
    rw [hcomm, he]
  rw [bodyLayer, Set.image_diff e.injective, himg, himg]
