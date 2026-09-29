-- Prove2me | Definitions.Def_Tropical_MultiInvariant_Core
-- name    : Tropical_MultiInvariant_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:35:52.161379+00:00
-- url     : https://prove2.me/theorems/bf4b2ce8-5673-4d24-9415-83f66a0a7bb2
-- title:
--   Aether Catalog definitions — Tropical_MultiInvariant_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.MultiInvariant.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/MultiInvariant/Core.lean by skeleton subtraction
import Mathlib
/-
# Multi-Invariant Theory Morphisms and Product Orders

This file develops the theory of **multi-invariant theory morphisms**: a framework
where a single morphism can transport multiple logically independent certificates
simultaneously, with full compositional clarity.

The key idea is that invariants live in product orders `Fin k → ℕ` (ordered pointwise),
so a single formal morphism carries, e.g., height + entropy + rank + robustness at once.

## Main Results

- `RichTheory` and `RichHom`: structures for k-invariant theories and their morphisms
- `RichHom.comp_mono_inv`: composition preserves the monotonicity property
- `scalar_to_rich_coordinate`: the scalar framework embeds as the k=1 special case
- `ScalarHom.toRich_faithful`: the embedding is faithful
- `scalar_hom_iff_rich_hom`: conservativity of enrichment
- `composite_dominates_source/intermediate/min`: dominance under composition
- `pairTheory` and `mk_pair_rich_hom`: bundling independent scalar certificates
- `mk_fin_rich_hom`: general finite-family bundling
- `CertTheory` and `CertHom`: preorder-valued generalization
-/


/-! ## Core Definitions -/

/-- A `RichTheory k` is a type equipped with `k` natural-number-valued invariants. -/
structure RichTheory (k : ℕ) where
  Carrier : Type
  Inv : Carrier → Fin k → ℕ

/-- A `RichHom T₁ T₂` is a function between carriers that is coordinatewise non-increasing
    on invariants: for every element and every coordinate, the image's invariant is at most
    the source's invariant. This ensures upper bounds transfer forward. -/
structure RichHom {k : ℕ} (T₁ T₂ : RichTheory k) where
  toFun : T₁.Carrier → T₂.Carrier
  mono_inv : ∀ x i, T₂.Inv (toFun x) i ≤ T₁.Inv x i

/-! ## Identity and Composition -/

/-- The identity morphism on a rich theory. -/
@[simps]
def RichHom.id {k : ℕ} (T : RichTheory k) : RichHom T T where
  toFun := _root_.id
  mono_inv := fun _ _ => le_refl _

/-- Composition of rich morphisms. -/
@[simps]
def RichHom.comp {k : ℕ} {T₁ T₂ T₃ : RichTheory k}
    (g : RichHom T₂ T₃) (f : RichHom T₁ T₂) : RichHom T₁ T₃ where
  toFun := g.toFun ∘ f.toFun
  mono_inv := fun x i => le_trans (g.mono_inv (f.toFun x) i) (f.mono_inv x i)

/-! ## Simp Lemmas for Identity and Composition -/



/-! ## Composition Theorem -/




/-! ## Scalar Theory and Embedding into k=1 -/

/-- A scalar theory: a type with a single ℕ-valued invariant. -/
structure ScalarTheory where
  Carrier : Type
  Inv : Carrier → ℕ

/-- A scalar morphism: a function that is non-increasing on the scalar invariant. -/
structure ScalarHom (T₁ T₂ : ScalarTheory) where
  toFun : T₁.Carrier → T₂.Carrier
  mono_inv : ∀ x, T₂.Inv (toFun x) ≤ T₁.Inv x

/-- Embed a scalar theory into a 1-invariant rich theory. -/
def ScalarTheory.toRich (T : ScalarTheory) : RichTheory 1 where
  Carrier := T.Carrier
  Inv := fun x _ => T.Inv x

/-- Embed a scalar morphism into a rich morphism. -/
def ScalarHom.toRich {T₁ T₂ : ScalarTheory} (f : ScalarHom T₁ T₂) :
    RichHom T₁.toRich T₂.toRich where
  toFun := f.toFun
  mono_inv := fun x _ => f.mono_inv x




/-! ## Dominance Theorems -/




/-! ## Pair Theory: Bundling Two Scalar Certificates -/

/-- Construct a 2-invariant theory from two scalar invariants on the same carrier. -/
def pairTheory (α : Type) (I₁ I₂ : α → ℕ) : RichTheory 2 where
  Carrier := α
  Inv := fun x i => match i with
    | ⟨0, _⟩ => I₁ x
    | ⟨1, _⟩ => I₂ x



/-- **Bundling theorem**: given two independent scalar certificate-transfer lemmas,
    assemble them into a single rich morphism on the paired theory. -/
def mk_pair_rich_hom
    {α β : Type} {I₁ I₂ : α → ℕ} {J₁ J₂ : β → ℕ}
    (f : α → β)
    (h₁ : ∀ x, J₁ (f x) ≤ I₁ x)
    (h₂ : ∀ x, J₂ (f x) ≤ I₂ x) :
    RichHom (pairTheory α I₁ I₂) (pairTheory β J₁ J₂) where
  toFun := f
  mono_inv := fun x i => by
    match i with
    | ⟨0, _⟩ => exact h₁ x
    | ⟨1, _⟩ => exact h₂ x



/-! ## Stretch: General Finite-Family Bundling -/


/-! ## Associativity and Unit Laws -/




/-! ## Preorder-Valued Generalization -/

/-- A certificate theory over a preorder: a type equipped with an invariant
    taking values in a preorder `L`. This generalizes `RichTheory` to
    arbitrary value lattices. -/
structure CertTheory (L : Type) [Preorder L] where
  Carrier : Type
  Inv : Carrier → L

/-- A certificate morphism: a function that is non-increasing on the invariant
    in a preorder-valued theory. -/
structure CertHom (L : Type) [Preorder L]
    (T₁ T₂ : CertTheory L) where
  toFun : T₁.Carrier → T₂.Carrier
  mono_inv : ∀ x, T₂.Inv (toFun x) ≤ T₁.Inv x






/-- **Finite-family bundling theorem**: given `k` independent scalar certificate-transfer
    lemmas, assemble them into a single rich morphism. This upgrades the pair construction
    to arbitrary finite collections and turns the framework into a theorem factory. -/
def mk_fin_rich_hom
    {k : ℕ} {α β : Type}
    {I : Fin k → α → ℕ} {J : Fin k → β → ℕ}
    (f : α → β)
    (h : ∀ i x, J i (f x) ≤ I i x) :
    RichHom
      { Carrier := α, Inv := fun x i => I i x }
      { Carrier := β, Inv := fun y i => J i y } where
  toFun := f
  mono_inv := fun x i => h i x

/-! ## Application Examples -/

/-- Example using `mk_fin_rich_hom` to bundle 3 invariants at once. -/
example : let I : Fin 3 → ℕ → ℕ := ![_root_.id, (· * 2), (· * 3)]
    let J : Fin 3 → ℕ → ℕ := ![(· / 2), _root_.id, _root_.id]
    RichHom
      { Carrier := ℕ, Inv := fun n i => I i n }
      { Carrier := ℕ, Inv := fun n i => J i n } :=
  mk_fin_rich_hom _root_.id (fun i x => by
    fin_cases i <;> simp [_root_.id, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega)


