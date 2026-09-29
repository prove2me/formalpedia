-- Prove2me | Definitions.Def_Bridges_TropicalPhylogenetics
-- name    : Bridges_TropicalPhylogenetics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:43.862615+00:00
-- url     : https://prove2.me/theorems/b1d09324-36f7-4728-b3e1-4d2de66a42de
-- title:
--   Aether Catalog definitions — Bridges_TropicalPhylogenetics
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalPhylogenetics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalPhylogenetics.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Language Evolution: Min-Plus Phylogenetics and Glottochronology

This module formalizes lexical evolution as min-plus geometry on language profiles,
establishing that tropical divergence is an exact phylogenetic distance recoverable
from tree-structured lexical drift.

## Main Definitions

* `TropLang` — A language over lexical universe `ι`, represented as `ι → ℝ`.
* `tropicalDivergence` — The L¹ coordinatewise divergence between languages.
* `tropicalSegmentCost` — The L∞ (sup-norm) tropical distance.
* `coordMedian3` — Coordinatewise median of three languages.
* `glottoTimeEstimate` — Divergence time estimator via normalized tropical divergence.
* `IsBetween` — Coordinatewise betweenness predicate for language profiles.
* `FourPointCond` — The four-point condition characterizing tree metrics.

## Main Results

### Metric Structure (Section 1)
* `tropicalDivergence_nonneg` — Tropical divergence is nonnegative.
* `tropicalDivergence_self` — Distance to self is zero.
* `tropicalDivergence_symm` — Symmetry of tropical divergence.
* `tropicalDivergence_triangle` — Triangle inequality.
* `tropicalDivergence_eq_zero_iff` — Separating property.

### Path Additivity (Section 2)
* `tropicalDivergence_additive_of_between` — Divergence is additive along
  geodesic paths where intermediates are coordinatewise between endpoints.

### Coordinatewise Median Optimality (Section 3)
* `coordMedian3_minimizes` — The median minimizes total divergence to three points.

### Glottochronology (Section 4)
* `glottochronology_from_tropical_divergence` — Divergence time is recovered
  from normalized tropical path length.

### Four-Point Condition and Tree Metrics (Section 5)
* `ultrametric_implies_fourPoint'` — Ultrametric spaces satisfy the four-point condition.
* `tropicalDivergence_fourPoint_fin1` — Four-point condition for 1D language profiles.
-/

noncomputable section

open Finset BigOperators

/-! ## Core Definitions -/

/-- A language over lexical universe `ι` is a cost profile assigning
a real-valued divergence score to each lexical item. -/
def TropLang (ι : Type*) := ι → ℝ

instance {ι : Type*} : CoeFun (TropLang ι) (fun _ => ι → ℝ) := ⟨id⟩

/-- Tropical divergence: the L¹ distance between language profiles.
Sums the absolute coordinatewise differences. This is the fundamental
phylogenetic distance functional. -/
def tropicalDivergence {ι : Type*} [Fintype ι]
    (L₁ L₂ : TropLang ι) : ℝ :=
  ∑ i : ι, |L₁ i - L₂ i|



/-- Coordinatewise betweenness: `M` lies between `A` and `B` if for every
coordinate, `M i` is between `A i` and `B i`. -/
def IsBetween {ι : Type*} (A M B : TropLang ι) : Prop :=
  ∀ i, (A i ≤ M i ∧ M i ≤ B i) ∨ (B i ≤ M i ∧ M i ≤ A i)

/-- Coordinatewise median of three language profiles. -/
def coordMedian3 {ι : Type*} (A B C : TropLang ι) : TropLang ι :=
  fun i => max (min (A i) (B i)) (max (min (A i) (C i)) (min (B i) (C i)))

/-- Glottochronological time estimate: tropical divergence normalized by rate. -/
def glottoTimeEstimate {ι : Type*} [Fintype ι]
    (ρ : ℝ) (L₁ L₂ : TropLang ι) : ℝ :=
  tropicalDivergence L₁ L₂ / ρ

/-- The four-point condition for a distance function, characterizing tree metrics. -/
def FourPointCond {V : Type*} (d : V → V → ℝ) : Prop :=
  ∀ a b c e,
    d a b + d c e ≤ max (d a c + d b e) (d a e + d b c)


/-! ## Section 1: Tropical Divergence is a Metric -/

/-
Tropical divergence is nonnegative.
-/

/-
Tropical divergence of a language with itself is zero.
-/

/-
Tropical divergence is symmetric.
-/

/-
Triangle inequality for tropical divergence.
-/

/-
Tropical divergence separates points.
-/

/-! ## Section 2: Path Additivity and Tree Distances -/

/-
Absolute value is additive when the intermediate point is between endpoints.
-/

/-
**Theorem A (two-step path additivity).** If `M` is coordinatewise between
`A` and `B`, then tropical divergence is additive. This is the fundamental
path-additivity theorem: divergence along tree paths decomposes exactly
when intermediates represent ancestral languages.
-/

/-
Path additivity extends to three-step paths: if M₁ is between A and M₂,
and M₂ is between M₁ and B, and M₁ is between A and B, then divergence
decomposes across the full path.
-/

/-! ## Section 3: Coordinatewise Median -/

/-
The median of three real numbers: max(min(a,b), max(min(a,c), min(b,c))).
-/

/-
The coordinatewise median lies between A and B for each coordinate.
-/

/-
**Median optimality theorem.** The coordinatewise median of three
languages minimizes the total tropical divergence to all three.
This is the ancestral reconstruction principle: the optimal common
ancestor is the coordinatewise median.
-/

/-! ## Section 4: Glottochronology -/

/-
**Theorem B: Glottochronology from tropical divergence.**
If tropical divergence scales linearly with tree path distance
at rate `ρ`, the divergence time is recovered by normalizing.
-/

/-! ## Section 5: Four-Point Condition -/

/-- An ultrametric distance: satisfies `d(a,c) ≤ max(d(a,b), d(b,c))`. -/
structure UltrametricDist {V : Type*} (d : V → V → ℝ) : Prop where
  dist_self : ∀ a, d a a = 0
  dist_symm : ∀ a b, d a b = d b a
  dist_nonneg : ∀ a b, 0 ≤ d a b
  ultra : ∀ a b c, d a c ≤ max (d a b) (d b c)

/-
Ultrametric implies four-point condition.
-/

/-
The four-point condition is preserved under nonneg scaling.
-/

/-! ## Section 6: Tropical Algebra -/

/-
Addition distributes over min (the min-plus semiring identity).
-/

/-
Right-distributivity of addition over min.
-/

/-! ## Section 7: Star Tree Four-Point Condition -/

/-
The pointwise four-point condition for real numbers: for any four reals,
`|p-q| + |r-s| ≤ max(|p-r|+|q-s|, |p-s|+|q-r|)`.
-/

/-
Tropical divergence rewrites when languages are center + drift.
-/

/-
The L¹ tropical divergence satisfies the four-point condition
for one-dimensional language profiles (`ι = Fin 1`), since ℝ
is itself a tree metric space. This is the base case from which
higher-dimensional tree models are built via coordinatewise constraints.
-/

/-! ## Section 8: Tropical Divergence Congr and Additional Properties -/


/-
Tropical divergence under additive shift: shifting both languages by
the same vector preserves divergence.
-/

end


