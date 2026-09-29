-- Prove2me | Definitions.Def_Bridges_UltrametricObserverConceptDuality
-- name    : Bridges_UltrametricObserverConceptDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:26.625428+00:00
-- url     : https://prove2.me/theorems/b602f10a-c676-4473-bfdd-77e93ecf5742
-- title:
--   Aether Catalog definitions — Bridges_UltrametricObserverConceptDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricObserverConceptDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricObserverConceptDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Ultrametric Observer–Concept Duality via Laminar Hierarchical Classifiers

This file formalizes a bridge between **ultrametric observer systems** (from speculative
proof semantics / non-Archimedean geometry) and **hierarchical concept classes** (from
machine learning / computational learning theory).

The central insight is that **finite ultrametric geometry is exactly the right substrate
for tree-structured concept classes**: ultrametric balls are automatically laminar
(nested or disjoint), and this laminarity is equivalent to hierarchical classifier
structure.

## Main Results

- `natBall_eq_of_mem`: Every point of an ultrametric ball is a center.
- `natBalls_nested_or_disjoint`: Two ultrametric balls are nested or disjoint.
- `natBalls_laminar`: All ultrametric balls form a laminar family.
- `stableBalls_laminar`: Stable balls of an observer system are laminar.
- `diagonalStable_auto`: Diagonal stability is automatic for ultrametric systems.
- `observer_perturbation_inclusion`: Perturbation stability for ball inclusion.
- `observerSystem_to_conceptSemimodule`: Forward direction of the duality.
- `finsetLaminar_chain`: Laminar family members containing a point form a chain.
- `ultrametric_isosceles_max`: Ultrametric isosceles triangle theorem.
- `certified_compression_from_laminarity`: Compression from laminarity.

## Bridge Connections

- **Ultrametric geometry ↔ Hierarchical learning**: Balls = laminar concept regions.
- **Prime separation ↔ Join-irreducibles**: Separation levels = tree branching.
- **Tropical decomposition** (`certified_finite_tropical_decomposition`): Finite
  idempotent generation → compression witnesses via ultrametric upgrade.
- **Diagonal stability ↔ Robustness**: Observer perturbation → classifier stability.
-/

open Finset Function Set

noncomputable section

/-! ## §1. Ultrametric Foundations -/

/-- A discrete ultrametric on a type `α` with ℕ-valued distances. -/
structure NatUltrametric (α : Type*) where
  d : α → α → ℕ
  d_self : ∀ a, d a a = 0
  d_symm : ∀ a b, d a b = d b a
  d_pos : ∀ a b, d a b = 0 → a = b
  d_ultra : ∀ a b c, d a c ≤ max (d a b) (d b c)

/-- Closed ball of radius `r` centered at `a`. -/
def NatBall {α : Type*} (um : NatUltrametric α) (a : α) (r : ℕ) : Set α :=
  {x | um.d a x ≤ r}



/-- **Key lemma**: Every point of an ultrametric ball is a center. -/
theorem natBall_eq_of_mem {α : Type*} (um : NatUltrametric α)
    {a x : α} {r : ℕ} (hx : x ∈ NatBall um a r) :
    NatBall um x r = NatBall um a r := by
  ext y; simp only [NatBall, Set.mem_setOf_eq] at *
  constructor
  · intro hy
    exact le_trans (le_trans (um.d_ultra a x y) (max_le_max hx hy)) (le_of_eq (max_self r))
  · intro hy
    have hxa : um.d x a ≤ r := by rw [um.d_symm]; exact hx
    exact le_trans (le_trans (um.d_ultra x a y) (max_le_max hxa hy)) (le_of_eq (max_self r))


/-! ## §2. Core Laminarity Theorem -/

/-- **Core theorem**: Two ultrametric balls are nested or disjoint. -/
theorem natBalls_nested_or_disjoint {α : Type*} (um : NatUltrametric α)
    (a b : α) (ra rb : ℕ) :
    NatBall um a ra ⊆ NatBall um b rb ∨
    NatBall um b rb ⊆ NatBall um a ra ∨
    Disjoint (NatBall um a ra) (NatBall um b rb) := by
  by_cases h : (NatBall um a ra ∩ NatBall um b rb).Nonempty
  · obtain ⟨z, hz⟩ := h
    have hza : z ∈ NatBall um a ra := hz.1
    have hzb : z ∈ NatBall um b rb := hz.2
    rw [← natBall_eq_of_mem um hza, ← natBall_eq_of_mem um hzb]
    by_cases hle : ra ≤ rb
    · left; intro x hx; simp only [NatBall, Set.mem_setOf_eq] at *; omega
    · right; left; intro x hx; simp only [NatBall, Set.mem_setOf_eq] at *; omega
  · right; right
    rw [Set.disjoint_iff]
    intro x ⟨hxa, hxb⟩
    exact h ⟨x, hxa, hxb⟩

/-- A family of sets is **laminar** if any two members are nested or disjoint. -/
def LaminarFamily' {α : Type*} (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B


/-- Any subfamily of a laminar family is laminar. -/
theorem laminarFamily'_mono {α : Type*} {F G : Set (Set α)}
    (hF : LaminarFamily' F) (hGF : G ⊆ F) : LaminarFamily' G :=
  fun A hA B hB => hF A (hGF hA) B (hGF hB)

/-- **Ultrametric balls form a laminar family.** -/
theorem natBalls_laminar {α : Type*} (um : NatUltrametric α) :
    LaminarFamily' {S | ∃ a r, S = NatBall um a r} := by
  intro A hA B hB
  obtain ⟨a, ra, rfl⟩ := hA
  obtain ⟨b, rb, rfl⟩ := hB
  exact natBalls_nested_or_disjoint um a b ra rb

/-! ## §3. Ultrametric Observer Systems -/

/-- An **ultrametric observer system** on a type `α`. -/
structure UltrametricObserverSystem (α : Type*) where
  um : NatUltrametric α
  stableRadii : Finset ℕ
  centers : Finset α

/-- The collection of stable balls. -/
def stableBalls {α : Type*} (O : UltrametricObserverSystem α) : Set (Set α) :=
  {S | ∃ a ∈ O.centers, ∃ r ∈ O.stableRadii, S = NatBall O.um a r}

/-- **Stable balls are laminar.** -/
theorem stableBalls_laminar {α : Type*} (O : UltrametricObserverSystem α) :
    LaminarFamily' (stableBalls O) := by
  apply laminarFamily'_mono (natBalls_laminar O.um)
  intro S hS; obtain ⟨a, _, r, _, rfl⟩ := hS; exact ⟨a, r, rfl⟩

/-- An observer system is **separated**. -/
def ObserverSeparated {α : Type*} (O : UltrametricObserverSystem α) : Prop :=
  ∀ x y : α, x ≠ y → ∃ S ∈ stableBalls O, x ∈ S ∧ y ∉ S

/-! ## §4. Laminar Concept Semimodule -/

/-- A **laminar concept semimodule**: a laminar family with ∅ and univ. -/
structure LaminarConceptSemimodule (α : Type*) where
  concepts : Set (Set α)
  laminar : LaminarFamily' concepts
  has_ground : Set.univ ∈ concepts
  has_empty : ∅ ∈ concepts

/-- Construct a laminar concept semimodule from an observer system. -/
def observerToSemimodule {α : Type*}
    (O : UltrametricObserverSystem α) :
    LaminarConceptSemimodule α where
  concepts := stableBalls O ∪ {Set.univ, ∅}
  laminar := by
    intro A hA B hB
    rcases hA with hA | hA
    · rcases hB with hB | hB
      · exact stableBalls_laminar O A hA B hB
      · rcases hB with rfl | rfl
        · left; exact Set.subset_univ A
        · right; left; exact Set.empty_subset A
    · rcases hA with rfl | rfl
      · right; left; exact Set.subset_univ B
      · left; exact Set.empty_subset _
  has_ground := Or.inr (Or.inl rfl)
  has_empty := Or.inr (Or.inr rfl)


/-! ## §5. Diagonal Stability -/

/-- Diagonal stability: smaller radius → smaller ball. -/
def DiagonalStable {α : Type*} (O : UltrametricObserverSystem α) : Prop :=
  ∀ r₁ r₂ : ℕ, r₁ ∈ O.stableRadii → r₂ ∈ O.stableRadii → r₁ ≤ r₂ →
  ∀ a ∈ O.centers, NatBall O.um a r₁ ⊆ NatBall O.um a r₂


/-- Separation level of two points. -/
def separationLevel {α : Type*} (um : NatUltrametric α) (x y : α) : ℕ := um.d x y



/-! ## §6. Perturbation Robustness -/



/-! ## §7. Compression Witnesses -/

/-- A **compression witness**: points that separate all distinct concepts. -/
structure CompressionWitness {α : Type*} (C : Set (Set α)) where
  witnesses : Finset α
  separates : ∀ S T : Set α, S ∈ C → T ∈ C → S ≠ T →
    ∃ w ∈ witnesses, (w ∈ S ∧ w ∉ T) ∨ (w ∉ S ∧ w ∈ T)

/-
**Certified compression from laminarity.**
-/

/-! ## §8. Finset Laminar Families -/

/-- Laminar family for `Finset`-based families. -/
def FinsetLaminar {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B


/-! ## §9. Join-Irreducibles -/


/-! ## §10. Observer–Concept Duality -/



/-! ## §11. The Concept Class -/

/-- The concept class of an observer system. -/
def ConceptClassOf {α : Type*} (O : UltrametricObserverSystem α) : Set (Set α) :=
  stableBalls O


/-! ## §12. Ultrametric Isosceles Triangle -/

/-
**Isosceles triangle**: if `d(a,b) ≠ d(b,c)`, then
    `d(a,c) = max(d(a,b), d(b,c))`.
-/

/-! ## §13. Bridge to Tropical Decomposition

The `certified_finite_tropical_decomposition` theorem establishes that finite max-plus
linear functionals have certified generators. In our setting, stable observer balls act
as tropical/idempotent generators. Ultrametricity upgrades generic tropical decomposition
to **laminar** decomposition: generators are nested or disjoint, giving tree-structured
classifiers with canonical reconstruction.

This bridge shows that tropical algebra (idempotent analysis) and ultrametric geometry
are not just analogous but structurally equivalent for finite concept hierarchies. -/


end


