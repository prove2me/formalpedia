-- Prove2me | Definitions.Def_Bridges_TropicalSatakePolytopeDuality
-- name    : Bridges_TropicalSatakePolytopeDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:07.42278+00:00
-- url     : https://prove2.me/theorems/13197d59-a4b4-4206-99ca-7ef029f6767c
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakePolytopeDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakePolytopeDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakePolytopeDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Satake Polytope Duality via Idempotent Weight Semimodules
  and Certified Crystal Reconstruction

This file establishes a finite, combinatorial bridge between tropical convex
geometry and crystal representation theory. The central result is that
multiplicity-free finite crystals are completely determined (up to canonical
isomorphism) by their tropical weight support profiles.

## Main Results

* `crystalSupportProfile` — functor from finite crystals to tropical weight profiles
* `exists_trivial_realization` — every profile admits a multiplicity-free crystal realization
* `reconstruction_operator_free` — two mult-free operator-free crystals with the same
  support profile are canonically isomorphic
* `extremal_weight_support_correspondence` — extremal weights equal support
* `mult_free_card_eq_support` — cardinality equals support size
* `iso_implies_same_profile` — isomorphic crystals have the same support profile

## Mathematical Context

In crystal base theory (Kashiwara), a highest-weight crystal is a colored directed
graph encoding the combinatorial skeleton of an irreducible representation. The weight
support of such a crystal is a finite subset of the weight lattice.

The tropical Satake perspective reinterprets weight supports as elements of a tropical
(idempotent) semimodule. This file proves that this reinterpretation is faithful in the
multiplicity-free regime: the tropical shadow completely determines the crystal structure.
-/


open Finset Function

/-! ## Section 1: Finite Root Datum -/

/-- A finite root datum: an index set for simple roots and a weight type. -/
structure FiniteRootDatum where
  ι : Type
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  P : Type
  [decEq_P : DecidableEq P]
  simpleRoot : ι → P

attribute [instance] FiniteRootDatum.fintype_ι FiniteRootDatum.decEq_ι
attribute [instance] FiniteRootDatum.decEq_P

namespace TropicalSatake

variable {R : FiniteRootDatum}

/-! ## Section 2: Tropical Weight Profile -/

/-- A tropical weight profile: a finite set of weights with a distinguished highest weight. -/
structure TropicalWeightProfile (R : FiniteRootDatum) where
  support : Finset R.P
  highestWeight : R.P
  hw_mem : highestWeight ∈ support


/-! ## Section 3: Finite Crystal -/

/-- A finite crystal: a colored directed graph with Kashiwara-style operators. -/
structure FiniteCrystal (R : FiniteRootDatum) where
  B : Type
  [fintype_B : Fintype B]
  [decEq_B : DecidableEq B]
  wt : B → R.P
  e : R.ι → B → Option B
  f : R.ι → B → Option B
  highest : B
  highest_not_raisable : ∀ i, e i highest = none
  ef_partial_inv : ∀ i b b', f i b = some b' → e i b' = some b
  fe_partial_inv : ∀ i b b', e i b = some b' → f i b' = some b

attribute [instance] FiniteCrystal.fintype_B FiniteCrystal.decEq_B

/-! ## Section 4: Crystal Support Profile -/

/-- The support profile of a finite crystal: the image of the weight map. -/
noncomputable def crystalSupportProfile (R : FiniteRootDatum) (K : FiniteCrystal R) :
    TropicalWeightProfile R where
  support := Finset.image K.wt Finset.univ
  highestWeight := K.wt K.highest
  hw_mem := Finset.mem_image_of_mem K.wt (Finset.mem_univ K.highest)

/-! ## Section 5: Key Definitions -/

/-- A crystal is multiplicity-free if the weight map is injective. -/
def MultFree (K : FiniteCrystal R) : Prop := Injective K.wt

/-- A crystal realizes a profile if its support profile equals that profile. -/
def RealizesProfile (K : FiniteCrystal R) (χ : TropicalWeightProfile R) : Prop :=
  crystalSupportProfile R K = χ

/-- A crystal is operator-free if all Kashiwara operators return none. -/
def OperatorFree (K : FiniteCrystal R) : Prop :=
  (∀ i b, K.e i b = none) ∧ (∀ i b, K.f i b = none)

/-! ## Section 6: Crystal Isomorphism -/

/-- A crystal isomorphism: a bijection preserving weights, operators, and highest weight. -/
structure CrystalIso (K₁ K₂ : FiniteCrystal R) where
  toEquiv : K₁.B ≃ K₂.B
  wt_comm : ∀ b, K₂.wt (toEquiv b) = K₁.wt b
  f_comm : ∀ i b, K₂.f i (toEquiv b) = (K₁.f i b).map toEquiv
  e_comm : ∀ i b, K₂.e i (toEquiv b) = (K₁.e i b).map toEquiv
  highest_comm : toEquiv K₁.highest = K₂.highest

/-! ## Section 7: Singleton Crystal -/

/-- A singleton crystal with just one vertex at a given weight. -/
def singletonCrystal (R : FiniteRootDatum) (p : R.P) : FiniteCrystal R where
  B := Unit
  wt := fun _ => p
  e := fun _ _ => none
  f := fun _ _ => none
  highest := ()
  highest_not_raisable := fun _ => rfl
  ef_partial_inv := fun _ _ _ h => by simp at h
  fe_partial_inv := fun _ _ _ h => by simp at h



/-! ## Section 8: Trivial Crystal from a Profile -/

/-- Trivial crystal: one vertex per support element, no Kashiwara edges. -/
noncomputable def trivialCrystal (R : FiniteRootDatum) (χ : TropicalWeightProfile R) :
    FiniteCrystal R where
  B := χ.support
  wt := Subtype.val
  e := fun _ _ => none
  f := fun _ _ => none
  highest := ⟨χ.highestWeight, χ.hw_mem⟩
  highest_not_raisable := fun _ => rfl
  ef_partial_inv := fun _ _ _ h => by simp at h
  fe_partial_inv := fun _ _ _ h => by simp at h




/-! ## Section 9: Existence Theorems -/



/-! ## Section 10: Reflexive Crystal Isomorphism -/


/-! ## Section 11: Isomorphism implies same profile -/

/-
If two crystals are isomorphic, they have the same support profile.
-/

/-! ## Section 12: Cardinality preservation -/


/-
In a multiplicity-free crystal, vertex count equals support size.
-/

/-! ## Section 13: Extremal Vertices -/


/-- The set of extremal (sink) vertices. -/
noncomputable def extremalVertices (K : FiniteCrystal R) : Finset K.B :=
  Finset.univ.filter (fun b => ∀ i, K.f i b = none)

/-- The set of source (highest-weight-type) vertices. -/
noncomputable def sourceVertices (K : FiniteCrystal R) : Finset K.B :=
  Finset.univ.filter (fun b => ∀ i, K.e i b = none)


/-- Extremal weights: the weight images of sink vertices. -/
noncomputable def extremalWeights (K : FiniteCrystal R) : Finset R.P :=
  (extremalVertices K).image K.wt

/-- Source weights: the weight images of source vertices. -/
noncomputable def sourceWeights (K : FiniteCrystal R) : Finset R.P :=
  (sourceVertices K).image K.wt

/-
The highest weight is always a source weight.
-/

/-! ## Section 14: Operator-free extremal correspondence -/

/-
In an operator-free crystal, every vertex is extremal.
-/

/-
In an operator-free crystal, every vertex is a source.
-/

/-
In an operator-free mult-free crystal, extremal weights equal support.
-/

/-! ## Section 15: Partial Inverse Properties -/

/-
The f operator is injective: if f_i(b₁) = f_i(b₂) = some c, then b₁ = b₂.
-/

/-
The e operator is injective: if e_i(b₁) = e_i(b₂) = some c, then b₁ = b₂.
-/

/-
The highest weight element is never the result of lowering.
-/

/-! ## Section 16: Profile determines weight image -/

/-
Same support profile implies same weight image.
-/

/-
Same support profile implies same highest weight.
-/

/-! ## Section 17: Weight Bijection -/

/-- Given two mult-free crystals with the same weight image, there exists
    a weight-preserving bijection. We construct it using Fintype.bijective_iff_surjective. -/
noncomputable def weightMatchFun
    (K₁ K₂ : FiniteCrystal R) (_hK₁ : MultFree K₁) (_hK₂ : MultFree K₂)
    (h_img : Finset.image K₁.wt Finset.univ = Finset.image K₂.wt Finset.univ)
    (b : K₁.B) : K₂.B :=
  (Finset.mem_image.mp (h_img ▸ Finset.mem_image_of_mem K₁.wt (Finset.mem_univ b))).choose

theorem weightMatchFun_spec
    (K₁ K₂ : FiniteCrystal R) (hK₁ : MultFree K₁) (hK₂ : MultFree K₂)
    (h_img : Finset.image K₁.wt Finset.univ = Finset.image K₂.wt Finset.univ)
    (b : K₁.B) :
    K₂.wt (weightMatchFun K₁ K₂ hK₁ hK₂ h_img b) = K₁.wt b := by
  exact (Finset.mem_image.mp (h_img ▸ Finset.mem_image_of_mem K₁.wt (Finset.mem_univ b))).choose_spec.2

noncomputable def weightBijection
    (K₁ K₂ : FiniteCrystal R) (hK₁ : MultFree K₁) (hK₂ : MultFree K₂)
    (h_img : Finset.image K₁.wt Finset.univ = Finset.image K₂.wt Finset.univ) :
    K₁.B ≃ K₂.B where
  toFun := weightMatchFun K₁ K₂ hK₁ hK₂ h_img
  invFun := weightMatchFun K₂ K₁ hK₂ hK₁ h_img.symm
  left_inv := by
    intro b
    apply hK₁
    rw [weightMatchFun_spec K₂ K₁ hK₂ hK₁ h_img.symm,
        weightMatchFun_spec K₁ K₂ hK₁ hK₂ h_img]
  right_inv := by
    intro b
    apply hK₂
    rw [weightMatchFun_spec K₁ K₂ hK₁ hK₂ h_img,
        weightMatchFun_spec K₂ K₁ hK₂ hK₁ h_img.symm]



/-! ## Section 18: Reconstruction Theorem for Operator-Free Crystals -/

/-
**Main Reconstruction Theorem (Operator-Free Case)**:
    Two multiplicity-free operator-free crystals with the same support profile
    are canonically isomorphic.

    This is the fundamental result: in the operator-free regime, the tropical
    weight support is a complete invariant for crystal structure.
-/

/-! ## Section 19: Crystal Morphism -/



/-! ## Section 20: Additional Correspondence Theorems -/



end TropicalSatake


