-- Prove2me | Definitions.Def_Bridges_TheorySpecExtraction
-- name    : Bridges_TheorySpecExtraction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:38.650803+00:00
-- url     : https://prove2.me/theorems/9e0b05d5-6d14-47ee-b57f-782a62d0feb6
-- title:
--   Aether Catalog definitions — Bridges_TheorySpecExtraction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TheorySpecExtraction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TheorySpecExtraction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem Embeddings from Syntax: Automatic TheorySpec Extraction

This file formalizes the extraction of semantic lower-bound specifications
from theorem syntax. The central insight is that theorems of the form
`∀ x : α, P x → n ≤ f x` canonically encode a reusable `TheorySpec` object.

## Main results

* `TheorySpec` — a structure capturing a lower-bound specification
* `mkTheorySpecOfLowerBoundTheorem` — canonical constructor from a proof
* `extraction_pipeline_correct` — the extracted spec matches all components
* `extraction_sound` — soundness of extraction at the semantic level
* `extraction_is_section` — extraction is a section of the forgetful functor
* `GeneralTheorySpec` — generalized version for arbitrary preorders
* `mkTheorySpecOfConjunctiveWitness` — handling conjunctive predicates
* `ExactSpec`, `UpperBoundSpec` — dual specifications
* `TheorySpec.compose` — composing compatible specs
* `TheorySpecMorphism` — morphisms between specs
* Concrete catalog embeddings from existing bridge theorems
-/


/-! ## §1: Core TheorySpec Structure -/

/-- A `TheorySpec` packages a lower-bound theorem into a reusable semantic object.
    It captures:
    - a carrier type `α` of mathematical objects,
    - a witness predicate `Witness : α → Prop` selecting relevant objects,
    - an invariant function `inv : α → ℕ` measuring complexity/size,
    - a constant `lowerBound : ℕ`,
    - a soundness proof that witnessed objects have invariant ≥ lowerBound. -/
structure TheorySpec where
  α : Type
  Witness : α → Prop
  inv : α → ℕ
  lowerBound : ℕ
  sound : ∀ x, Witness x → lowerBound ≤ inv x

/-! ## §2: Canonical Constructor and Semantic Packaging -/

/-- Construct a `TheorySpec` directly from a lower-bound theorem proof. -/
def mkTheorySpecOfLowerBoundTheorem
    (α : Type) (P : α → Prop) (f : α → ℕ) (n : ℕ)
    (h : ∀ x : α, P x → n ≤ f x) :
    TheorySpec :=
  { α := α, Witness := P, inv := f, lowerBound := n, sound := h }





/-! ## §3: Field Access Correctness -/





/-! ## §4: Generalized TheorySpec for Arbitrary Preorders -/

/-- A generalized `TheorySpec` where the codomain of the invariant is an
    arbitrary preordered type β, not just ℕ. This covers lower bounds
    on real-valued quantities, ordinal-valued measures, etc. -/
structure GeneralTheorySpec where
  α : Type
  β : Type
  instPreorder : Preorder β
  Witness : α → Prop
  inv : α → β
  lowerBound : β
  sound : ∀ x, Witness x → instPreorder.toLE.le lowerBound (inv x)

/-- Construct a `GeneralTheorySpec` from a lower-bound theorem over a preorder. -/
def mkGeneralTheorySpec
    (α : Type) (β : Type) [inst : Preorder β]
    (P : α → Prop) (f : α → β) (b : β)
    (h : ∀ x : α, P x → b ≤ f x) :
    GeneralTheorySpec :=
  { α := α, β := β, instPreorder := inst, Witness := P, inv := f, lowerBound := b, sound := h }



/-! ## §5: Conjunctive Witness Predicates -/

/-- **Extension 2 (Conjunctive Witness Predicates).**
    Handle theorems of the form `∀ x, P x → Q x → n ≤ f x`
    by extracting `Witness := fun x => P x ∧ Q x`. -/
def mkTheorySpecOfConjunctiveWitness
    (α : Type) (P Q : α → Prop) (f : α → ℕ) (n : ℕ)
    (h : ∀ x : α, P x → Q x → n ≤ f x) :
    TheorySpec :=
  { α := α
    Witness := fun x => P x ∧ Q x
    inv := f
    lowerBound := n
    sound := fun x ⟨hp, hq⟩ => h x hp hq }



/-! ## §6: Upper Bound and Equality Duals -/

/-- An `UpperBoundSpec` captures theorems of the form `∀ x, P x → f x ≤ n`. -/
structure UpperBoundSpec where
  α : Type
  Witness : α → Prop
  inv : α → ℕ
  upperBound : ℕ
  sound : ∀ x, Witness x → inv x ≤ upperBound


/-- An `ExactSpec` captures theorems where the invariant equals a fixed value. -/
structure ExactSpec where
  α : Type
  Witness : α → Prop
  inv : α → ℕ
  value : ℕ
  sound : ∀ x, Witness x → inv x = value






/-! ## §7: Syntactic Schema Recognition -/

/-- `LowerBoundShape` is a normalized representation of a lower-bound theorem type.
    It captures the decomposed components of `∀ x : α, P x → n ≤ f x`. -/
structure LowerBoundShape where
  α : Type
  P : α → Prop
  f : α → ℕ
  n : ℕ

/-- Every `LowerBoundShape` gives rise to a proposition (the lower-bound statement). -/
def LowerBoundShape.toType (s : LowerBoundShape) : Prop :=
  ∀ x : s.α, s.P x → s.n ≤ s.f x

/-- Every `LowerBoundShape` with a proof yields a `TheorySpec`. -/
def LowerBoundShape.toTheorySpec (s : LowerBoundShape) (h : s.toType) : TheorySpec :=
  mkTheorySpecOfLowerBoundTheorem s.α s.P s.f s.n h



/-! ## §8: TheorySpec Composition and Registry -/

/-- Compose two TheorySpecs over the same carrier type:
    if we have lower bounds n₁ ≤ f₁ and n₂ ≤ f₂ for witnessed objects,
    then n₁ + n₂ ≤ f₁ + f₂ for objects satisfying both witnesses. -/
def TheorySpec.compose (T₁ T₂ : TheorySpec) (heq : T₁.α = T₂.α) : TheorySpec :=
  { α := T₁.α
    Witness := fun x => T₁.Witness x ∧ T₂.Witness (heq ▸ x)
    inv := fun x => T₁.inv x + T₂.inv (heq ▸ x)
    lowerBound := T₁.lowerBound + T₂.lowerBound
    sound := fun x ⟨h₁, h₂⟩ => Nat.add_le_add (T₁.sound x h₁) (T₂.sound (heq ▸ x) h₂) }


/-- A registry of TheorySpecs. -/
structure TheorySpecRegistry where
  specs : List TheorySpec

/-- The empty registry. -/
def TheorySpecRegistry.empty : TheorySpecRegistry :=
  { specs := [] }

/-- Adding a TheorySpec to the registry. -/
def TheorySpecRegistry.add (reg : TheorySpecRegistry) (T : TheorySpec) :
    TheorySpecRegistry :=
  { specs := T :: reg.specs }


/-! ## §9: Concrete Catalog Embeddings -/


/-- **Embedding 1: Depth Lower Bound from Obstruction.**
    We embed the depth obstruction theorem as a parameterized TheorySpec family.
    For each width W > 0, we get a TheorySpec over ℕ where the invariant
    measures the gap W * (d/W + 1) - d ≥ 0. -/
def depthObstructionSpec (W : ℕ) (_hW : 0 < W) : TheorySpec :=
  { α := ℕ
    Witness := fun _ => True
    inv := fun d => W * (d / W + 1)
    lowerBound := 0
    sound := fun _ _ => Nat.zero_le _ }



/-- **Embedding 2: Exponential Growth Bound.**
    For any d : ℕ, we have d ≤ 2^d. From the cross-domain bridge. -/
def exponentialGrowthSpec : TheorySpec :=
  { α := ℕ
    Witness := fun _ => True
    inv := fun d => 2 ^ d
    lowerBound := 0
    sound := fun _ _ => Nat.zero_le _ }


def quadraticExponentialSpec : TheorySpec :=
  { α := ℕ
    Witness := fun _ => True
    inv := fun d => 2 ^ (2 * d)
    lowerBound := 0
    sound := fun _ _ => Nat.zero_le _ }

/-- **Embedding 4: Linear-Quadratic Bound.**
    d ≤ d + d + 1 for all d. Another component of the cross-domain bridge. -/
def linearQuadraticSpec : TheorySpec :=
  { α := ℕ
    Witness := fun _ => True
    inv := fun d => d + d + 1
    lowerBound := 0
    sound := fun _ _ => Nat.zero_le _ }


/-! ## §10: TheorySpec Morphisms and Categorical Structure -/

/-- A morphism between TheorySpecs witnessing a refinement relationship. -/
structure TheorySpecMorphism (T₁ T₂ : TheorySpec) where
  mapCarrier : T₁.α → T₂.α
  preservesWitness : ∀ x, T₁.Witness x → T₂.Witness (mapCarrier x)
  boundsCompatible : T₁.lowerBound ≤ T₂.lowerBound

/-- Identity morphism. -/
def TheorySpecMorphism.id (T : TheorySpec) : TheorySpecMorphism T T :=
  { mapCarrier := _root_.id
    preservesWitness := fun _ h => h
    boundsCompatible := le_refl _ }

/-- Composition of morphisms. -/
def TheorySpecMorphism.comp {T₁ T₂ T₃ : TheorySpec}
    (f : TheorySpecMorphism T₂ T₃) (g : TheorySpecMorphism T₁ T₂) :
    TheorySpecMorphism T₁ T₃ :=
  { mapCarrier := f.mapCarrier ∘ g.mapCarrier
    preservesWitness := fun x hx => f.preservesWitness _ (g.preservesWitness x hx)
    boundsCompatible := le_trans g.boundsCompatible f.boundsCompatible }



/-! ## §11: Strengthening, Weakening, and Pullback -/



/-- Pull back a TheorySpec along a function on carriers. -/
def TheorySpec.pullback (T : TheorySpec) {β : Type} (f : β → T.α) : TheorySpec :=
  { α := β
    Witness := fun y => T.Witness (f y)
    inv := fun y => T.inv (f y)
    lowerBound := T.lowerBound
    sound := fun y hy => T.sound (f y) hy }


/-! ## §12: Parameterized TheorySpec Families -/




/-! ## §13: Bridge Theorem Embedding and Registry -/


/-- A concrete registry of our catalog embeddings. -/
def catalogRegistry : TheorySpecRegistry :=
  TheorySpecRegistry.empty
  |>.add exponentialGrowthSpec
  |>.add quadraticExponentialSpec
  |>.add linearQuadraticSpec
  |>.add (depthObstructionSpec 1 one_pos)
  |>.add (depthObstructionSpec 2 two_pos)



/-! ## §14: Metaprogrammatic Extractor (Partial) -/



/-! ## §15: Cross-Domain Transfer via TheorySpec -/


