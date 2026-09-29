-- Prove2me | solution 1 for TropicalVoronoiDecoderDuality.realization_from_partition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:10:23.227584+00:00
-- url     : https://prove2.me/submissions/db78b622-fc84-421a-b1c3-75e89bb6bcae

-- Sol generated from Bridges/TropicalVoronoiDecoderDuality.lean
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

/-
**Main Realization Theorem**: Every essential family with disjoint cells
    yields a canonical decoder complex where each covered point belongs to
    exactly one cell.
-/

/-! ## §12. Minimality = Essential Cell Count -/


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


open TropicalVoronoiDecoderDuality in
theorem solution    {n : ℕ} (parts : Fin n → Finset X)
    (hcover : ∀ x : X, ∃ i, x ∈ parts i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hnonempty : ∀ i, (parts i).Nonempty) :
    ∃ G : Finset (X → ℕ),
      G.card = n ∧
      EssentialFamily G ∧
      (∀ f ∈ G, ∀ g ∈ G, f ≠ g → Disjoint (decoderCell f G) (decoderCell g G)) := by
  by_contra! h_contra';
  -- Define the family G as the image of the map i ↦ (fun x => if x ∈ parts i then 0 else 1).
  set G : Finset (X → ℕ) := Finset.image (fun i => fun x => if x ∈ parts i then 0 else 1) (Finset.univ : Finset (Fin n));
  refine' absurd ( h_contra' G _ _ ) _;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    intro i j h; have := congr_fun h; simp_all +decide [ funext_iff, Finset.disjoint_left ] ;
    exact Classical.not_not.1 fun hi => by obtain ⟨ x, hx ⟩ := hnonempty i; specialize this x; specialize hdisjoint i j hi hx; aesop;
  · intro f hf; obtain ⟨ i, _, rfl ⟩ := Finset.mem_image.mp hf; use Classical.choose ( hnonempty i ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide [ Classical.choose_spec ( hnonempty i ) ] ⟩ ;
  · simp +decide [ Finset.disjoint_left, decoderCell ];
    intro f hf g hg hfg x hx; obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp hf; obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hg; simp_all +decide [ funext_iff ] ;
    by_cases hi : x ∈ parts i <;> by_cases hj : x ∈ parts j <;> simp_all +decide [ Finset.disjoint_left ];
    · exact hdisjoint i j ( by rintro rfl; exact hfg.elim fun x hx => hx <| by aesop ) hi hj;
    · exact ⟨ _, hf, if_pos hi ⟩;
    · exact absurd ( hx _ hg ) ( by simp +decide [ hj ] );
    · obtain ⟨ k, hk ⟩ := hcover x; specialize hx _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ k ) ) ; aesop;
