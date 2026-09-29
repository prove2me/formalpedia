-- Prove2me | Definitions.Def_Bridges_TropicalVoronoiDecoderDuality
-- name    : Bridges_TropicalVoronoiDecoderDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:00.613468+00:00
-- url     : https://prove2.me/theorems/a332b656-d6fc-4a54-95b0-7c092a400771
-- title:
--   Aether Catalog definitions — Bridges_TropicalVoronoiDecoderDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalVoronoiDecoderDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalVoronoiDecoderDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Voronoi–Lattice Realization Duality via Idempotent Distance Semimodules

This file formalizes a finite duality theorem connecting tropical nearest-site
geometry with algebraic classification of idempotent distance semimodules.

## Mathematical Setting

We work over a **finite ambient type** `X` with the min-plus (tropical) semiring
on `ℕ`. A "profile" is a function `X → ℕ` representing a tropical distance-like
cost. Given a finite family of profiles (generators), we form:

- **Decoder cells**: regions where each generator achieves the minimum cost
- **Tropical span**: the set of all pointwise-min combinations of shifted generators
- **Essential/separated families**: irredundancy and distinctness conditions

## Main Results

- `cells_cover` — Decoder cells cover the entire ambient space
- `essential_subfamily_exists` — Every nonempty family has an essential subfamily
- `essential_iff_nonempty_exclusive_cell` — Essentiality ↔ having an exclusive point
- `essential_family_card_le` — Essential families have ≤ |X| generators
- `separated_essential_determines_cells` — Cell complexes determine essential families
- `realization_from_cells` — Any partition of X can be realized by a decoder family
- `finite_tropical_voronoi_realization` — Main realization duality theorem
- `minimal_generators_eq_essential_cells` — Minimality = essential cell count
- `certified_reconstruction` — Reconstruction from cell incidence data

## Bridges

- **Algebra ↔ Geometry**: Tropical semimodules ↔ Voronoi decoder complexes
- **Coding Theory ↔ Tropical Algebra**: Decoder regions ↔ extremal rays
- **Metric Reconstruction ↔ Certification**: Recovery from inequality data
-/


open Finset Function

noncomputable section

namespace TropicalVoronoiDecoderDuality

/-! ## §1. Tropical Profile Operations

We work with `ℕ`-valued profiles on a finite type. The min-plus tropical
structure is:
- Tropical addition: `(f ⊕ g)(x) = min(f(x), g(x))`
- Tropical scalar multiplication: `(c ⊗ f)(x) = c + f(x)`
-/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Tropical (min-plus) addition of profiles: pointwise minimum. -/
def tropAdd (f g : X → ℕ) : X → ℕ := fun x => min (f x) (g x)

/-- Tropical scalar multiplication: shift by a constant. -/
def tropSmul (c : ℕ) (f : X → ℕ) : X → ℕ := fun x => c + f x





/-! ## §2. Decoder Cells

Given a profile `f` and a family `G` of profiles, the decoder cell of `f`
is the set of points where `f` achieves the minimum value among all profiles in `G`.
-/

/-- The decoder cell: points where `f` achieves the minimum over all `g ∈ G`. -/
def decoderCell (f : X → ℕ) (G : Finset (X → ℕ)) : Finset X :=
  Finset.univ.filter (fun x => ∀ g ∈ G, f x ≤ g x)



/-! ## §3. Cell Covering Theorem

Every point in `X` belongs to some decoder cell. -/

/-
The decoder cells of a nonempty family cover all of `X`.
-/

/-! ## §4. Separation and Essentiality -/


/-- A family is **essential** if every generator has a nonempty decoder cell. -/
def EssentialFamily (G : Finset (X → ℕ)) : Prop :=
  ∀ f ∈ G, (decoderCell f G).Nonempty

/-- A generator `f` has an **exclusive point** if there exists `x` where `f` is
    strictly less than all other generators. -/
def HasExclusivePoint (f : X → ℕ) (G : Finset (X → ℕ)) : Prop :=
  ∃ x : X, ∀ g ∈ G, g ≠ f → f x < g x

/-
If `f` has an exclusive point in `G`, then its decoder cell is nonempty.
-/

/-! ## §5. Essential Subfamily Extraction -/

/-- The essential subfamily: generators with nonempty decoder cells. -/
def essentialSubfamily (G : Finset (X → ℕ)) : Finset (X → ℕ) :=
  G.filter (fun f => (decoderCell f G).Nonempty)



/-! ## §6. Cardinality Bounds -/

/-
An essential family with pairwise disjoint cells has at most `|X|` generators.
-/

/-! ## §7. Tropical Span -/

/-- A profile `h` is in the tropical span of `G` if at each point x, h(x) equals
    some `c + g(x)` for some generator g ∈ G and constant c. -/
def InTropSpan (h : X → ℕ) (G : Finset (X → ℕ)) : Prop :=
  ∀ x : X, ∃ g ∈ G, ∃ c : ℕ, h x = c + g x


/-! ## §8. Distance Profiles -/

/-- A profile `f` is a **weighted tropical distance profile** if it arises as
    `f(x) = w + dist(x, p)` for some site `p` and weight `w`. -/
def IsWeightedDistProfile {P : Type*} (dist : X → P → ℕ) (f : X → ℕ) : Prop :=
  ∃ p : P, ∃ w : ℕ, f = fun x => w + dist x p


/-! ## §9. Cell Complex Structure -/

/-- The cell complex of a family: the collection of all nonempty decoder cells. -/
def cellComplex (G : Finset (X → ℕ)) : Finset (Finset X) :=
  (G.image (fun f => decoderCell f G)).filter Finset.Nonempty

/-- Two families are **cell-equivalent** if they induce the same cell complex. -/
def CellEquivalent (G₁ G₂ : Finset (X → ℕ)) : Prop :=
  cellComplex G₁ = cellComplex G₂




/-! ## §10. Tropical Equivalence of Profiles -/

/-- Two profiles are **tropically equivalent** if they differ by a global constant shift. -/
def TropEquiv (f g : X → ℕ) : Prop :=
  ∃ c : ℤ, ∀ x : X, (g x : ℤ) = (f x : ℤ) + c


-- Tropical equivalence is symmetric.

-- Tropical equivalence is transitive.

/-! ## §11. Main Realization Duality Theorem -/

/-
**Realization from partition**: Given a partition of `X` into nonempty parts,
    one can construct a separated essential family realizing those cells.
    This is the geometric → algebraic direction.
-/

/-
**Main Realization Theorem**: Every essential family with disjoint cells
    yields a canonical decoder complex where each covered point belongs to
    exactly one cell.
-/

/-! ## §12. Minimality = Essential Cell Count -/

/-- A subfamily `S ⊆ G` is **decoder-covering** if it covers the same points. -/
def DecoderCovering (S G : Finset (X → ℕ)) : Prop :=
  S ⊆ G ∧ ∀ x : X, (∃ f ∈ G, x ∈ decoderCell f G) →
    (∃ f ∈ S, x ∈ decoderCell f G)

/-
**Minimality Theorem**: In an essential family with disjoint cells,
    no proper subfamily is decoder-covering.
-/

/-
**Minimality = Cell Count**: The number of generators in an essential family
    with disjoint cells equals the number of nonempty cells.
-/

/-! ## §13. Reconstruction from Cell Data -/

/-
**Certified Reconstruction**: Two essential families with disjoint cells
    and the same cell complex have the same cardinality.
-/

/-! ## §14. Decoder Cell Monotonicity and Antitonicity -/

/-
Adding a generator to the family can only shrink decoder cells.
-/

/-
If `f` pointwise dominates `g` (i.e., `f x ≤ g x` for all x), then
    `f`'s decoder cell contains `g`'s decoder cell.
-/

/-! ## §15. Concrete Example: Three-Site Decoder on Fin 6 -/

/-- Example site profiles for a three-site decoder on 6 points. -/
def exSite1 : Fin 6 → ℕ := ![0, 1, 2, 3, 4, 5]
def exSite2 : Fin 6 → ℕ := ![5, 4, 3, 2, 1, 0]
def exSite3 : Fin 6 → ℕ := ![3, 2, 1, 1, 2, 3]

def exFamily : Finset (Fin 6 → ℕ) := {exSite1, exSite2, exSite3}

/-
The first site's decoder cell contains {0, 1}.
-/

/-
The second site's decoder cell contains {4, 5}.
-/

/-
The third site's decoder cell contains {2, 3}.
-/

/-
The example family is essential: every generator has a nonempty cell.
-/

/-
The example family has pairwise disjoint cells.
-/

end TropicalVoronoiDecoderDuality


