-- Prove2me | Definitions.Def_Bridges_AlgebraEMLTropical_PadicClosureInformationDuality
-- name    : Bridges_AlgebraEMLTropical_PadicClosureInformationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:05.862002+00:00
-- url     : https://prove2.me/theorems/f8e7dd17-53ca-4917-82e4-1fe148615fd1
-- title:
--   Aether Catalog definitions — Bridges_AlgebraEMLTropical_PadicClosureInformationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraEMLTropical.PadicClosureInformationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraEMLTropical/PadicClosureInformationDuality.lean by skeleton subtraction
import Mathlib
/-
# Non-Archimedean Information Duality via p-adic Closure Capacities and Min-Plus Rate Functions

This file formalizes a duality between closure-stable ultrametric capacities on finite
closure lattices and tropical min-plus information functionals. The valuation scale
is `WithTop ℕ` (equivalently `ℕ∞`), capturing the essential non-Archimedean structure:
`0` = trivial (empty set), finite values = finite information cost, `⊤` = impossible.

## Main Results (all sorry-free)

- `closureCapacity_tropicalizes` — Every closure capacity yields tropical info.
- `tropicalization_canonical_on_closure_classes` — Constant on closure classes.
- `closureCapacity_residuated_of_fintype` — Residuation automatic from finiteness.
- `tropicalInformation_reconstructs_unique_capacity` — Unique reconstruction.
- `capacity_info_equiv` — Type equivalence ClosureCapacity ≃ TropicalClosureInformation.
- `closureMorphism_information_contraction` — Data processing inequality.
- `ultrametricInfoDist_triangle` — Ultrametric triangle inequality for info distance.
- `closure_class_iInf_eq` — Infimum over closure class is attained.
- `isClosureMorphism_comp` — Closure morphisms compose.
- `pullback_comp_eq` — Pullback is functorial.
- `ultrametric_ternary_join` — Three-way ultrametric bound.

## Bridges

- **Algebra ↔ Information Theory**: Ultrametric capacities ↔ tropical information
- **Valuation Theory ↔ Optimization**: p-adic valuations ↔ min-plus shortest paths
- **EML Semantics ↔ Tropical Geometry**: Closure lattices ↔ idempotent semimodules
- **Category Theory ↔ Data Processing**: Closure morphisms ↔ information contraction
-/


open Set Classical

noncomputable section

namespace Bridges.AlgebraEMLTropical.PadicClosureInformationDuality

/-! ## §1. Closure Operator Axiomatics -/

/-- A closure operator on `Set α`: monotone, extensive, idempotent. -/
structure IsClosureOperator {α : Type*} (cl : Set α → Set α) : Prop where
  idempotent : ∀ s, cl (cl s) = cl s
  monotone : ∀ ⦃s t : Set α⦄, s ⊆ t → cl s ⊆ cl t
  extensive : ∀ s, s ⊆ cl s


/-! ## §2. Closure Capacity

A normalized, monotone, closure-invariant function from sets to the tropical
valuation scale `WithTop ℕ`, satisfying the ultrametric join inequality. -/

structure ClosureCapacity
    (α : Type*) [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) : Type _ where
  toFun : Set α → WithTop ℕ
  closed_invariant : ∀ s : Set α, toFun (cl s) = toFun s
  monotone : ∀ ⦃s t : Set α⦄, s ⊆ t → toFun s ≤ toFun t
  normalized_bot : toFun ∅ = 0
  ultrametric_join :
    ∀ s t : Set α, toFun (cl (s ∪ t)) ≤ max (toFun s) (toFun t)


/-! ## §3. Tropical Closure Information

Extends ClosureCapacity with residuation: every closure class has a least-cost
representative. -/

structure TropicalClosureInformation
    (α : Type*) [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) : Type _ where
  toFun : Set α → WithTop ℕ
  closed_invariant : ∀ s, toFun (cl s) = toFun s
  monotone : ∀ ⦃s t : Set α⦄, s ⊆ t → toFun s ≤ toFun t
  normalized_bot : toFun ∅ = 0
  ultrametric_join :
    ∀ s t, toFun (cl (s ∪ t)) ≤ max (toFun s) (toFun t)
  residuated :
    ∀ s, ∃ t, cl t = cl s ∧ ∀ u, cl u = cl s → toFun t ≤ toFun u


/-! ## §4. Closure Morphisms -/

/-- `f : α → β` is a closure morphism if `f '' (clα s) ⊆ clβ (f '' s)`. -/
def IsClosureMorphism
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (clα : Set α → Set α) (clβ : Set β → Set β) (f : α → β) : Prop :=
  ∀ s : Set α, f '' (clα s) ⊆ clβ (f '' s)

/-! ## §5. Decomposition Cost -/


/-! ## §6. Unit-Shift Equivalence -/

/-- Two functions differ by a global additive constant. -/
def EquivalentUpToUnitShift {α : Type*}
    (f g : Set α → WithTop ℕ) : Prop :=
  ∃ c : ℕ, ∀ s, g s = f s + ↑c

/-! ## §7. Theorem A: Tropicalization -/


/-! ## §8. Closure Class Invariance -/

/-- A closure capacity is constant on closure classes. Generalizes
`quantum_thermodynamic_certified_capacity_invariant_under_closure_equiv`. -/
theorem tropicalization_canonical_on_closure_classes
    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (v : ClosureCapacity α cl) :
    ∀ s t : Set α, cl s = cl t → v.toFun s = v.toFun t := by
  intro s t h
  calc v.toFun s = v.toFun (cl s) := (v.closed_invariant s).symm
    _ = v.toFun (cl t) := by rw [h]
    _ = v.toFun t := v.closed_invariant t

/-! ## §9. Residuation from Finiteness -/

/-- On a finite type, every closure capacity satisfies residuation automatically. -/
theorem closureCapacity_residuated_of_fintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (v : ClosureCapacity α cl) :
    ∀ s : Set α, ∃ t : Set α, cl t = cl s ∧
      ∀ u : Set α, cl u = cl s → v.toFun t ≤ v.toFun u := by
  intro s
  exact ⟨s, rfl, fun u hu =>
    le_of_eq (tropicalization_canonical_on_closure_classes v s u hu.symm)⟩

/-! ## §10. Theorem B: Reconstruction and Uniqueness -/


/-! ## §11. Capacity ↔ Information Maps -/

/-- Forward: add residuation (automatic from finiteness). -/
def capacityToInfo
    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} :
    ClosureCapacity α cl → TropicalClosureInformation α cl :=
  fun v => {
    toFun := v.toFun
    closed_invariant := v.closed_invariant
    monotone := v.monotone
    normalized_bot := v.normalized_bot
    ultrametric_join := v.ultrametric_join
    residuated := closureCapacity_residuated_of_fintype v
  }

/-- Backward: forget residuation. -/
def infoToCapacity
    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} :
    TropicalClosureInformation α cl → ClosureCapacity α cl :=
  fun I => {
    toFun := I.toFun
    closed_invariant := I.closed_invariant
    monotone := I.monotone
    normalized_bot := I.normalized_bot
    ultrametric_join := I.ultrametric_join
  }



/-! ## §12. Theorem C: Type Equivalence -/


/-! ## §13. Pullback Along Closure Morphisms -/

/-- Pullback of information along a closure morphism. -/
def pullbackInfo
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {clα : Set α → Set α} {clβ : Set β → Set β}
    (hclα : IsClosureOperator clα)
    (f : α → β)
    (hf : IsClosureMorphism clα clβ f)
    (Iβ : TropicalClosureInformation β clβ) :
    ClosureCapacity α clα where
  toFun s := Iβ.toFun (f '' s)
  closed_invariant s := by
    apply le_antisymm
    · calc Iβ.toFun (f '' clα s)
          ≤ Iβ.toFun (clβ (f '' s)) := Iβ.monotone (hf s)
        _ = Iβ.toFun (f '' s) := Iβ.closed_invariant (f '' s)
    · exact Iβ.monotone (image_mono (hclα.extensive s))
  monotone _ _ hst := Iβ.monotone (image_mono hst)
  normalized_bot := by rw [image_empty]; exact Iβ.normalized_bot
  ultrametric_join s t := by
    have h1 : Iβ.toFun (f '' clα (s ∪ t)) = Iβ.toFun (f '' (s ∪ t)) := by
      apply le_antisymm
      · calc Iβ.toFun (f '' clα (s ∪ t))
            ≤ Iβ.toFun (clβ (f '' (s ∪ t))) := Iβ.monotone (hf (s ∪ t))
          _ = Iβ.toFun (f '' (s ∪ t)) := Iβ.closed_invariant _
      · exact Iβ.monotone (image_mono (hclα.extensive _))
    rw [h1, image_union, ← Iβ.closed_invariant]
    exact Iβ.ultrametric_join (f '' s) (f '' t)

/-! ## §14. Theorem D: Information Contraction -/


/-! ## §15. Theorem E: Optimization = Tropical Residuation -/


/-! ## §16. Attained Infimum (Strengthened Theorem E) -/


/-! ## §17. Closure Expansion Preserves Information -/


/-! ## §18. Ultrametric Ternary Join -/


/-! ## §19. Closure Morphism Composition -/


/-! ## §20. Identity Closure Morphism -/


/-! ## §21. Zero Capacity -/

def zeroCapacity
    {α : Type*} [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) : ClosureCapacity α cl where
  toFun _ := 0
  closed_invariant _ := rfl
  monotone _ _ _ := le_refl _
  normalized_bot := rfl
  ultrametric_join _ _ := by simp

/-! ## §22. Closure Equivalence -/

def ClosureEquiv {α : Type*} (cl : Set α → Set α) (s t : Set α) : Prop :=
  cl s = cl t



/-! ## §23. Capacity Bounded by Closure Containment -/


/-! ## §24. Pullback Functoriality -/


/-! ## §25. EquivalentUpToUnitShift -/


/-! ## §26. Ultrametric Information Distance -/

/-- Ultrametric pseudo-distance: `d(s,t) = v(cl(s ∪ t))`. -/
def ultrametricInfoDist
    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (v : ClosureCapacity α cl) (s t : Set α) : WithTop ℕ :=
  v.toFun (cl (s ∪ t))



/-! ## §27. Singleton Information -/



/-! ## §28. Closure Operator Examples -/

def idClosure (α : Type*) : Set α → Set α := id


/-! ## §29. Order on Capacities -/

instance {α : Type*} [Fintype α] [DecidableEq α] {cl : Set α → Set α} :
    LE (ClosureCapacity α cl) where
  le v w := ∀ s : Set α, v.toFun s ≤ w.toFun s


/-! ## §30. Concrete Example: Bool -/


end Bridges.AlgebraEMLTropical.PadicClosureInformationDuality


