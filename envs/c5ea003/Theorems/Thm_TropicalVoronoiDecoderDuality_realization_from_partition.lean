-- Prove2me | Theorems.Thm_TropicalVoronoiDecoderDuality_realization_from_partition
-- name    : TropicalVoronoiDecoderDuality.realization_from_partition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:04.829037+00:00
-- url     : https://prove2.me/theorems/27913411-c895-44a8-beb4-f4af0240c569
-- title:
--   Realization from partition
-- statement:
--   Formal statement of `TropicalVoronoiDecoderDuality.realization_from_partition` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalVoronoiDecoderDuality.realization_from_partition    {n : ℕ} (parts : Fin n → Finset X)
--       (hcover : ∀ x : X, ∃ i, x ∈ parts i)
--       (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
--       (hnonempty : ∀ i, (parts i).Nonempty) :
--       ∃ G : Finset (X → ℕ),
--         G.card = n ∧
--         EssentialFamily G ∧
--         (∀ f ∈ G, ∀ g ∈ G, f ≠ g → Disjoint (decoderCell f G) (decoderCell g G)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalVoronoiDecoderDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalVoronoiDecoderDuality.lean#L246

-- Thm stub generated from Bridges/TropicalVoronoiDecoderDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalVoronoiDecoderDuality
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

open TropicalVoronoiDecoderDuality

/-! ## §1. Tropical Profile Operations

We work with `ℕ`-valued profiles on a finite type. The min-plus tropical
structure is:
- Tropical addition: `(f ⊕ g)(x) = min(f(x), g(x))`
- Tropical scalar multiplication: `(c ⊗ f)(x) = c + f(x)`
-/

variable {X : Type*} [Fintype X] [DecidableEq X]







/-! ## §2. Decoder Cells

Given a profile `f` and a family `G` of profiles, the decoder cell of `f`
is the set of points where `f` achieves the minimum value among all profiles in `G`.
-/




/-! ## §3. Cell Covering Theorem

Every point in `X` belongs to some decoder cell. -/

/-
The decoder cells of a nonempty family cover all of `X`.
-/

/-! ## §4. Separation and Essentiality -/




/-
If `f` has an exclusive point in `G`, then its decoder cell is nonempty.
-/

/-! ## §5. Essential Subfamily Extraction -/




/-! ## §6. Cardinality Bounds -/

/-
An essential family with pairwise disjoint cells has at most `|X|` generators.
-/

/-! ## §7. Tropical Span -/



/-! ## §8. Distance Profiles -/



/-! ## §9. Cell Complex Structure -/






/-! ## §10. Tropical Equivalence of Profiles -/



-- Tropical equivalence is symmetric.

-- Tropical equivalence is transitive.

/-! ## §11. Main Realization Duality Theorem -/

/-
**Realization from partition**: Given a partition of `X` into nonempty parts,
    one can construct a separated essential family realizing those cells.
    This is the geometric → algebraic direction.
-/

theorem TropicalVoronoiDecoderDuality.realization_from_partition    {n : ℕ} (parts : Fin n → Finset X)
    (hcover : ∀ x : X, ∃ i, x ∈ parts i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hnonempty : ∀ i, (parts i).Nonempty) :
    ∃ G : Finset (X → ℕ),
      G.card = n ∧
      EssentialFamily G ∧
      (∀ f ∈ G, ∀ g ∈ G, f ≠ g → Disjoint (decoderCell f G) (decoderCell g G)) := by sorry
