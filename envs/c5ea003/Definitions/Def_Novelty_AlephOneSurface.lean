-- Prove2me | Definitions.Def_Novelty_AlephOneSurface
-- name    : Novelty_AlephOneSurface
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:50.897173+00:00
-- url     : https://prove2.me/theorems/2d5394b8-e61d-4f97-aff2-cc810a5400bd
-- title:
--   Aether Catalog definitions — Novelty_AlephOneSurface
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AlephOneSurface`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AlephOneSurface.lean by skeleton subtraction
import Mathlib

/-!
# The Aleph-One Surface: Geometry Between the Dimensions

This file develops the geometry of the **Hilbert cube**
`Q = ℕ → [0,1]`, the canonical compact space that lives *between* the finite
dimensions and the transfinite.  The guiding question is a classical one dressed
in modern clothing:

> Is there a bounded, compact "surface" that refuses to fit inside any
> finite-dimensional Euclidean space, yet remains a tame, metrizable continuum?

The Hilbert cube answers *yes*.  We assemble a self-contained account of three
intertwined phenomena.

*Cardinality (a set-theoretic bridge).* The cube has exactly the cardinality of
the continuum, and — remarkably — so does every positive-dimensional Euclidean
space.  Thus **cardinality alone can never detect dimension**: the naive count of
points is blind to the geometric chasm between `ℝⁿ` and `Q`.  Under the Continuum
Hypothesis this common cardinal is precisely the first uncountable cardinal
`ℵ₁`, so the cube is literally a *surface of size `ℵ₁`*.

*Transfinite dimensionality (a topological witness).* For **every** finite `n`
the `n`-dimensional cube embeds into `Q` as a genuine topological subspace.
No finite dimension is large enough to contain the whole cube: `Q` sits strictly
above every `ℝⁿ` in dimension even though it is a single compact metrizable
object.

*Self-similarity (geometry between dimensions).* The cube is homeomorphic to its
own square, `Q ≃ Q × Q`, and — the signature of infinite dimension — to itself
with one extra coordinate glued on, `Q ≃ Q × [0,1]`.  Adding a dimension changes
nothing: this is exactly the behaviour a finite cube can never exhibit, and it is
why the cube has no finite triangulation into cells of bounded dimension.

## Main results

* `AlephOneSurface.hilbertCube_card` — the cube has cardinality `𝔠`.
* `AlephOneSurface.euclidean_card` — every `ℝⁿ` (`n ≥ 1`) has cardinality `𝔠`.
* `AlephOneSurface.card_cannot_detect_dimension` — cube and `ℝⁿ` are
  equinumerous, so counting points is dimension-blind.
* `AlephOneSurface.hilbertCube_card_of_CH` — under CH the cube has cardinality
  `ℵ₁`.
* `AlephOneSurface.cube_isEmbedding` / `AlephOneSurface.contains_every_finite_cube`
  — every finite cube embeds topologically into `Q`.
* `AlephOneSurface.hilbertCube_prod_self` — `Q ≃ Q × Q`.
* `AlephOneSurface.hilbertCube_add_coordinate` — `Q ≃ Q × [0,1]`.
-/

open Topology Cardinal

namespace AlephOneSurface

/-- The **Hilbert cube** `Q`, realised as the countable power of the unit
interval.  A point is an infinite sequence of coordinates in `[0,1]`. -/
abbrev HilbertCube : Type := ℕ → unitInterval

/-!
## Basic topology of the cube

The cube is a compact, metrizable, second-countable connected continuum.  These
structural facts are what make it a legitimate "surface" rather than a pathology,
and they are used freely in the embedding and self-similarity arguments below.
-/






/-!
## Cardinality: a bridge from set theory to geometry

The cube has continuum-many points.  So does every positive-dimensional
Euclidean space.  Consequently no cardinal invariant can distinguish the two,
which is precisely why *topology* (not counting) is needed to separate the
finite dimensions from the transfinite.
-/








/-!
## Transfinite dimensionality: every finite cube lives inside `Q`

We construct, for each `n`, an explicit topological embedding of the finite cube
`[0,1]ⁿ` into `Q`: place the `n` coordinates first and pad the tail with zeros.
The tail-truncation map is a continuous left inverse, which upgrades the padding
map to an embedding.  Since this works for *all* `n`, the cube contains subspaces
of arbitrarily large finite dimension and hence cannot embed in any single
`ℝᵐ`.
-/

/-- Pad a finite cube point into the Hilbert cube by filling the tail with `0`. -/
def cubeSection (n : ℕ) (x : Fin n → unitInterval) : HilbertCube :=
  fun k => if h : k < n then x ⟨k, h⟩ else 0

/-- Read off the first `n` coordinates of a Hilbert-cube point. -/
def cubeProj (n : ℕ) (x : HilbertCube) : Fin n → unitInterval := fun i => x i







/-!
## Self-similarity: the geometry between dimensions

The defining feature of infinite dimension is *dimensional indifference*: the
cube is homeomorphic to its own square, and gluing on one extra interval
coordinate leaves it unchanged.  A finite cube can never do this, and it is the
obstruction to any finite triangulation of bounded cell-dimension.
-/

/-- A bijection `ℕ ≃ ℕ ⊕ ℕ` used to split the coordinates of the cube into two
countable halves. -/
noncomputable def splitCoords : ℕ ≃ ℕ ⊕ ℕ := (Denumerable.eqv (ℕ ⊕ ℕ)).symm

/-- A bijection `ℕ ≃ ℕ ⊕ Unit` used to peel off a single coordinate. -/
noncomputable def peelCoord : ℕ ≃ ℕ ⊕ Unit :=
  (Denumerable.eqv (Option ℕ)).symm.trans (Equiv.optionEquivSumPUnit ℕ)

/-- **The Hilbert cube is homeomorphic to its own square:** `Q ≃ Q × Q`.  This
self-similarity is impossible for any finite cube. -/
noncomputable def hilbertCube_prod_self : HilbertCube ≃ₜ HilbertCube × HilbertCube :=
  (Homeomorph.piCongrLeft (Y := fun _ : ℕ ⊕ ℕ => unitInterval) splitCoords).trans
    Homeomorph.sumArrowHomeomorphProdArrow

/-- **Adding a dimension changes nothing:** `Q ≃ Q × [0,1]`.  The cube absorbs an
extra interval coordinate up to homeomorphism, the hallmark of a space that lies
beyond every finite dimension. -/
noncomputable def hilbertCube_add_coordinate : HilbertCube ≃ₜ HilbertCube × unitInterval :=
  ((Homeomorph.piCongrLeft (Y := fun _ : ℕ ⊕ Unit => unitInterval) peelCoord).trans
      Homeomorph.sumArrowHomeomorphProdArrow).trans
    ((Homeomorph.refl _).prodCongr (Homeomorph.funUnique Unit unitInterval))


/-!
-- !-- Lab Notes -- !--

**Category declaration.**  This cycle serves *both* menu categories at once:
it is a subtask of a famous open problem (the Continuum Hypothesis, whose
independence sits at the foundation of set theory) *and* an explicit bridge
between two domains — set-theoretic cardinal arithmetic and point-set topology.

**Hypothesis (Hypothesizer).**  A bounded compact "surface" can refuse every
finite Euclidean dimension while remaining metrizable; its point-set should have
the cardinality of the continuum, equal under CH to `ℵ₁`; and its defining
signature should be dimensional self-similarity `Q ≃ Q × Q`.

**Experiment (Experimenter).**  We realised the surface as the Hilbert cube
`ℕ → [0,1]`.  Compactness, metrizability, second-countability and connectedness
are structural.  Cardinality `𝔠` follows from `#[0,1] = 𝔠` and `𝔠 ^ ℵ₀ = 𝔠`.
The Euclidean comparison needed the auxiliary law `𝔠 ^ n = 𝔠` for `n ≥ 1`,
proved by squeezing between `𝔠 ^ 1` and `𝔠 ^ ℵ₀`.  Finite-cube embeddings use a
padding-by-zero section with continuous truncation as a left inverse.
Self-similarity uses the coordinate bijections `ℕ ≃ ℕ ⊕ ℕ` and `ℕ ≃ ℕ ⊕ Unit`
together with the exponential homeomorphism `(A ⊕ B → X) ≃ (A → X) × (B → X)`.

**Analysis (Analyst).**  What survived: all cardinality, embedding, and
self-similarity claims.  What needed a different definition: a literal
"Hausdorff dimension equal to `ℵ₁`" is a category error — Hausdorff dimension is
a real-valued (`≤ ∞`) invariant and cannot equal a cardinal.  The correct,
provable formulation of "transfinite dimension" is that the cube contains
embedded cubes of *every* finite dimension while being a single compact object;
this is the honest content and it is theorem-strength.  The would-be
"non-embeddability into `ℝⁿ`" in full generality requires invariance of domain
(dimension theory); we instead prove the constructive half — arbitrarily
high-dimensional cubes embed — and the cardinality obstruction that shows why
counting cannot see the gap.

**Critique (Critic).**  None of the main results is vacuous: cardinality
theorems compute a genuine cardinal, embeddings produce honest topological
subspaces (with a continuous left inverse, so genuinely inducing), and the
homeomorphisms are explicit data. The CH result is stated as a clean conditional,
faithfully reflecting the independence of CH — it assumes CH as a hypothesis and
does not smuggle it in. The self-similarity homeomorphisms are the sharp
witnesses distinguishing the cube from every finite cube.

**Synthesis (Principal Investigator).**  The Hilbert cube is the canonical
"surface between dimensions": continuum-many points (`ℵ₁` under CH), compact and
metrizable, containing every finite cube, and dimensionally self-similar. These
threads — set theory, topology, and geometry — meet in one object.
-/

end AlephOneSurface


