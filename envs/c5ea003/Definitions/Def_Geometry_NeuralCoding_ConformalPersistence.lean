-- Prove2me | Definitions.Def_Geometry_NeuralCoding_ConformalPersistence
-- name    : Geometry_NeuralCoding_ConformalPersistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:11.105286+00:00
-- url     : https://prove2.me/theorems/d957656f-8bc3-4944-8404-cae8cbf4e748
-- title:
--   Aether Catalog definitions — Geometry_NeuralCoding_ConformalPersistence
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.NeuralCoding.ConformalPersistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/NeuralCoding/ConformalPersistence.lean by skeleton subtraction
import Mathlib

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

namespace ConformalPersistence

open Finset

variable {n : ℕ}

/-- Squared Euclidean norm of a vector in `ℝⁿ`. -/
def nsq (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- Euclidean inner product on `ℝⁿ`. -/
def ip (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- Squared Euclidean distance on `ℝⁿ`. -/
def euclDist2 (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

/-
!-- comment -- !--
The master algebraic identity: expand a squared affine combination ∑(a xᵢ + b yᵢ)²
into norms and inner product. Everything downstream is a corollary of this `ring` fact.
!-- comment -- !--
-/



/-
`euclDist2` in terms of norms and inner product.
-/

/-- **Inverse stereographic projection** `φ : ℝⁿ → Sⁿ ⊂ ℝⁿ × ℝ`.
The image is encoded as a pair (the first `n` coordinates, the height coordinate). -/
def invStereoN (x : Fin n → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => 2 * x i / (1 + nsq x), (nsq x - 1) / (1 + nsq x))

/-- Squared norm of a point of `ℝⁿ × ℝ ≅ ℝⁿ⁺¹`. -/
def sphereNsq (p : (Fin n → ℝ) × ℝ) : ℝ := nsq p.1 + p.2 ^ 2

/-- Squared Euclidean (chordal) distance in the ambient `ℝⁿ⁺¹`. -/
def sphereDist2 (p q : (Fin n → ℝ) × ℝ) : ℝ := euclDist2 p.1 q.1 + (p.2 - q.2) ^ 2

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

/-- Chordal distance on the sphere between the two stereographic images. -/
def chordal (x y : Fin n → ℝ) : ℝ := Real.sqrt (sphereDist2 (invStereoN x) (invStereoN y))

/-- Conformally weighted Euclidean distance on `ℝⁿ`:
`d_w(x,y) = 2‖x-y‖ / √((1+‖x‖²)(1+‖y‖²))`. -/
def weightedDist (x y : Fin n → ℝ) : ℝ :=
  2 * Real.sqrt (euclDist2 x y) / Real.sqrt ((1 + nsq x) * (1 + nsq y))

/-
!-- comment -- !--
Theorem 3: taking square roots in Theorem 2 shows the chordal sphere metric equals the weighted
Euclidean metric exactly. This is the isometry (ℝⁿ, d_w) ≅ (Sⁿ, chordal).
!-- comment -- !--

**Theorem 3 (Isometry).** The chordal sphere distance equals the conformally weighted
Euclidean distance, point for point.
-/

/-- Vietoris–Rips edge predicate at scale `ε` for a distance `d`. -/
def VRedge (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (ε : ℝ) (x y : Fin n → ℝ) : Prop := d x y ≤ ε

/-
!-- comment -- !--
Theorem 4: since the two metrics are equal, the Vietoris–Rips filtration (edge set at every
scale ε), and therefore the full pairwise distance matrix of any point cloud, are identical.
Persistence diagrams are functions of this data, so they coincide.
!-- comment -- !--

**Theorem 4 (Persistence equality).** For every scale `ε`, the Vietoris–Rips edge set under
the spherical chordal metric equals the one under the weighted Euclidean metric; equivalently the
distance matrix of any finite point cloud is identical, so the persistence diagrams agree.
-/


/-
!-- comment -- !--
Bonus: the spherical GEODESIC distance is g(chordal) with g(c) = 2·arcsin(c/2), strictly
increasing on [0,2]. A strictly monotone reparametrization of the filtration leaves persistence
diagrams invariant, so the equality also holds for the geodesic metric.
!-- comment -- !--

**Theorem 5 (Geodesic monotonicity).** The geodesic-from-chordal map `c ↦ 2·arcsin(c/2)` is
strictly monotone on `[0,2]`, so spherical *geodesic* persistence is a monotone reparametrization
of chordal (= weighted Euclidean) persistence.
-/

end ConformalPersistence


