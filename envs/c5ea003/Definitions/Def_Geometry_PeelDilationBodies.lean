-- Prove2me | Definitions.Def_Geometry_PeelDilationBodies
-- name    : Geometry_PeelDilationBodies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:30.562384+00:00
-- url     : https://prove2.me/theorems/4d1ed81a-c1da-4d83-b1ac-b844aacec780
-- title:
--   Aether Catalog definitions — Geometry_PeelDilationBodies
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PeelDilationBodies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PeelDilationBodies.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
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

namespace Catalog.Geometry.Peel

open Finset MeasureTheory Metric Pointwise

/-! ## Volumes of dilates -/

/-- The Lebesgue measure of a body of `ℝ^d`, as a real number. -/
noncomputable def bodyVol (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (volume K).toReal

lemma bodyVol_nonneg (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : 0 ≤ bodyVol d K :=
  ENNReal.toReal_nonneg


/-- Scaling law: `vol (c • K) = c^d · vol K`. -/
lemma bodyVol_smul {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} {c : ℝ} (hc : 0 ≤ c) :
    bodyVol d (c • K) = c ^ d * bodyVol d K := by
  unfold bodyVol
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume hc K, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-! ## Star-shaped bodies and nested dilates -/

/-- `K` is star-shaped about the origin. -/
def StarShaped {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • x ∈ K


/-! ## The universal equal-volume dilation peeling -/

/-- The dilation factor of the `k`-th layer: `(1 - k/N)^{1/d}`, depending only
on the dimension and the number of layers. -/
noncomputable def dilationFactor (d N k : ℕ) : ℝ :=
  (max 0 (1 - (k : ℝ) / (N : ℝ))) ^ ((d : ℝ)⁻¹)






/-- The peeling profile of the dilation family of a body `K`. -/
noncomputable def bodyPeel (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (N : ℕ) : PeelProfile :=
  equipartitionProfile (bodyVol d K) (bodyVol_nonneg d K) N




/-- The `k`-th layer of the dilation peeling of `K`. -/
noncomputable def bodyLayer (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (N k : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  (dilationFactor d N k) • K \ (dilationFactor d N (k + 1)) • K



/-! ## Rigidity for arbitrary bodies -/

/-- The peeling profile attached to a dilation family of a star-shaped body. -/
noncomputable def dilationProfile (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → ℝ) (hanti : Antitone c) (hnn : ∀ k, 0 ≤ c k) : PeelProfile where
  size k := bodyVol d ((c k) • K)
  anti := by
    intro a b hab
    show bodyVol d ((c b) • K) ≤ bodyVol d ((c a) • K)
    rw [bodyVol_smul (hnn a), bodyVol_smul (hnn b)]
    have : c b ^ d ≤ c a ^ d := pow_le_pow_left₀ (hnn b) (hanti hab) d
    nlinarith [bodyVol_nonneg d K]
  nonneg := fun _ => bodyVol_nonneg d _



end Catalog.Geometry.Peel


