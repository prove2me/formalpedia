-- Prove2me | Theorems.Thm_ConformalPersistence_stereo_conformal_identity
-- name    : ConformalPersistence.stereo_conformal_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:09:39.935146+00:00
-- url     : https://prove2.me/theorems/5578db59-5582-44a4-981e-1a1ac7f88fcb
-- title:
--   Stereo conformal identity
-- statement:
--   Formal statement of `ConformalPersistence.stereo_conformal_identity` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ConformalPersistence.stereo_conformal_identity(x y : Fin n → ℝ) :
--       sphereDist2 (invStereoN x) (invStereoN y) * ((1 + nsq x) * (1 + nsq y))
--         = 4 * euclDist2 x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/NeuralCoding/ConformalPersistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/NeuralCoding/ConformalPersistence.lean#L120

-- Thm stub generated from Geometry/NeuralCoding/ConformalPersistence.lean
import Mathlib
import Definitions.Def_Geometry_NeuralCoding_ConformalPersistence

/-! # CatalogBuild.Geometry.ConformalPersistence

## Inverse Stereographic Persistence — Conformal Isometry on Sⁿ

This file develops the rigorous geometric backbone of *stereographic persistence*:
the claim that persistent homology of a point cloud on the sphere `Sⁿ`, computed with
the (chordal/geodesic) sphere metric, agrees with persistent homology of the inverse
stereographic image in `ℝⁿ` computed with a **conformally weighted** Euclidean distance.

We generalize the catalog's `S¹`-only results
(`Geometry.StereographicSheaf.stereoProj_on_circle`,
`Geometry.InverseStereoResearch.inv_stereo_on_circle`) to arbitrary dimension `n`, and we
connect them to the persistence framework of `Geometry.PrimewisePersistence` by proving that
inverse stereographic projection is an **exact isometry**
`(ℝⁿ, d_w) ≃ (Sⁿ ⊂ ℝⁿ⁺¹, chordal)`.  Because Vietoris–Rips / Čech filtrations depend only on
the pairwise distance matrix, an isometry forces *identical* persistence diagrams — turning the
"equal up to conformal factor" conjecture into an exact equality.

The conformal weight is encoded in the exact identity (Theorem `stereo_conformal_identity`):
  `‖φ(x) - φ(y)‖² · (1+‖x‖²)(1+‖y‖²) = 4 ‖x - y‖²`,
i.e. the chordal distance on the sphere equals `d_w(x,y) = 2‖x-y‖ / √((1+‖x‖²)(1+‖y‖²))`.

-- !-- Lab Notebook -- !--
Hypothesis: Inverse stereographic projection is not merely conformal "up to a factor" but is an
  *exact isometry* from ℝⁿ with a closed-form weighted distance to Sⁿ with the chordal metric;
  hence spherical persistence diagrams equal weighted-Euclidean persistence diagrams exactly.
Result: Proved (1) φ(x) ∈ Sⁿ for all n; (2) the exact conformal identity
  ‖φx-φy‖²(1+‖x‖²)(1+‖y‖²) = 4‖x-y‖²; (3) chordal = weighted distance; (4) Vietoris–Rips edge
  sets (hence the whole filtration / distance matrix) coincide; (5) the spherical *geodesic*
  metric is a strictly monotone reparametrization of the chordal metric, so persistence is
  preserved for the geodesic metric too.
Insight: The single algebraic identity `sum_affine_sq` (expanding ∑(a xᵢ + b yᵢ)²) reduces the
  whole conformal computation to scalar algebra in X=‖x‖², Y=‖y‖², P=⟨x,y⟩. The "conformal factor"
  is exactly the product of the two stereographic denominators (1+X)(1+Y).
Failure analysis: A naive attempt to phrase everything over `EuclideanSpace ℝ (Fin n)` drowns in
  coercions; working with bare `Fin n → ℝ` and an explicit `nsq`/`ip` keeps `ring`/`field_simp`
  effective. Stating the identity for the *squared* distances (avoiding √) is what makes it a pure
  `ring` fact; the √ form is then a one-line corollary.
-- !-- Lab Notebook -- !--
-/

noncomputable section

open ConformalPersistence

open Finset

variable {n : ℕ}




/-
!-- comment -- !--
The master algebraic identity: expand a squared affine combination ∑(a xᵢ + b yᵢ)²
into norms and inner product. Everything downstream is a corollary of this `ring` fact.
!-- comment -- !--
-/



/-
`euclDist2` in terms of norms and inner product.
-/




/-
!-- comment -- !--
Theorem 1 (generalizes catalog `inv_stereo_on_circle`/`stereoProj_on_circle` from S¹ to Sⁿ):
the inverse stereographic image lands on the unit sphere, in every dimension.
!-- comment -- !--

**Theorem 1.** Inverse stereographic projection lands on the unit sphere `Sⁿ`.
-/

/-
!-- comment -- !--
Theorem 2 (the gem): the EXACT conformal isometry identity. The "conformal factor" is exactly
the product of the two stereographic denominators (1+‖x‖²)(1+‖y‖²). Proof: rewrite the chordal
distance via `sum_affine_sq`, reduce to scalar algebra in X,Y,P, then `field_simp; ring`.
!-- comment -- !--

**Theorem 2 (Exact conformal identity).**
`‖φ(x)-φ(y)‖² · (1+‖x‖²)(1+‖y‖²) = 4 ‖x-y‖²`. This is the precise sense in which inverse
stereographic projection is a conformal isometry: the chordal sphere distance equals the weighted
Euclidean distance `2‖x-y‖/√((1+‖x‖²)(1+‖y‖²))`.
-/

theorem ConformalPersistence.stereo_conformal_identity(x y : Fin n → ℝ) :
    sphereDist2 (invStereoN x) (invStereoN y) * ((1 + nsq x) * (1 + nsq y))
      = 4 * euclDist2 x y := by sorry
