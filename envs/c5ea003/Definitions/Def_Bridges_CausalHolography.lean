-- Prove2me | Definitions.Def_Bridges_CausalHolography
-- name    : Bridges_CausalHolography
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:02.441288+00:00
-- url     : https://prove2.me/theorems/f99a90e6-d909-4bc5-9c3f-41674c55ab86
-- title:
--   Aether Catalog definitions — Bridges_CausalHolography
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CausalHolography`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CausalHolography.lean by skeleton subtraction
import Mathlib
/-
  # Idempotent Causal Holography via Closure Lightcone Semimodules

  This file formalizes a finite reconstruction theorem for causal closure systems.
  Given a finite poset C (the causal order) and a boundary subset B, we show that
  the bulk causal order can be canonically recovered from boundary past/future
  profile data.

  ## Main results

  * `order_embedding_of_separating_profiles` — Under separation and order reflection
    hypotheses, the profile map is an order embedding into compatible profile pairs.
  * `reconstructs_bulk_from_boundary_profiles` — Under interval generation, we get
    a full order isomorphism: the bulk IS the boundary profile poset.
  * `cover_reconstruction` — Cover relations are preserved and reflected.
  * `interval_reconstruction` — Alexandrov intervals are faithfully reconstructed.
-/


open Finset

/-! ## Core definitions -/

/-- A boundary antichain: no two distinct elements of B are comparable. -/
def isBoundaryAntichain {α : Type*} [PartialOrder α] (B : Finset α) : Prop :=
  ∀ ⦃x y⦄, x ∈ B → y ∈ B → x ≤ y → x = y

section Profiles

variable {α : Type*} [PartialOrder α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]

/-- Past profile: boundary elements below x. -/
def pastProfile (B : Finset α) (x : α) : Finset α :=
  B.filter (fun b => b ≤ x)

/-- Future profile: boundary elements above x. -/
def futureProfile (B : Finset α) (x : α) : Finset α :=
  B.filter (fun b => x ≤ b)

/-- The bi-profile map. -/
def profilePair (B : Finset α) (x : α) :
    Finset α × Finset α :=
  (pastProfile B x, futureProfile B x)

end Profiles

/-- Separation: profilePair is injective. -/
def separates_bulk {α : Type*} [PartialOrder α] [DecidableEq α]
    [DecidableRel (α := α) (· ≤ ·)] (B : Finset α) : Prop :=
  Function.Injective (profilePair B)

/-- The profile order: covariant in past, contravariant in future. -/
def profileLE {α : Type*} :
    (Finset α × Finset α) → (Finset α × Finset α) → Prop
  | (p₁, f₁), (p₂, f₂) => p₁ ⊆ p₂ ∧ f₂ ⊆ f₁

/-- A profile pair is compatible if every past boundary element
    is below every future boundary element. -/
def profile_compatible {α : Type*} [PartialOrder α]
    (B : Finset α) (q : Finset α × Finset α) : Prop :=
  ∀ ⦃bp bf⦄, bp ∈ q.1 → bf ∈ q.2 → bp ≤ bf

/-- Interval generation: every compatible profile pair with components in B is realized. -/
def interval_generated {α : Type*} [PartialOrder α] [DecidableEq α]
    [DecidableRel (α := α) (· ≤ ·)] (B : Finset α) : Prop :=
  ∀ q, profile_compatible B q → q.1 ⊆ B → q.2 ⊆ B → ∃ x, profilePair B x = q

/-- The set of reconstructed points: compatible profile pairs with components in B. -/
def reconstructedPoints {α : Type*} [PartialOrder α] [DecidableEq α] (B : Finset α) :=
  {q : Finset α × Finset α // profile_compatible B q ∧ q.1 ⊆ B ∧ q.2 ⊆ B}

/-- Cover relation: x < y with nothing strictly between. -/
def isCoverRel {α : Type*} [PartialOrder α] (x y : α) : Prop :=
  x < y ∧ ¬∃ z, x < z ∧ z < y

/-- Alexandrov interval. -/
def alexandrovInterval {α : Type*} [PartialOrder α] (x y : α) : Set α :=
  {z | x ≤ z ∧ z ≤ y}

/-! ## Helper lemmas -/

variable {α : Type*} [PartialOrder α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]




/-- Every point's profile pair is compatible. -/
theorem profile_compatible_of_point
    (B : Finset α) (x : α) :
    profile_compatible B (profilePair B x) :=
  fun _ _ hbp hbf =>
    (Finset.mem_filter.mp hbp).2.trans (Finset.mem_filter.mp hbf).2

/-- Past profile is a subset of B. -/
theorem pastProfile_subset
    (B : Finset α) (x : α) :
    pastProfile B x ⊆ B :=
  Finset.filter_subset _ _

/-- Future profile is a subset of B. -/
theorem futureProfile_subset
    (B : Finset α) (x : α) :
    futureProfile B x ⊆ B :=
  Finset.filter_subset _ _

/-- The profile data for a point satisfies all conditions for reconstructedPoints. -/
theorem profilePair_mem_reconstructed
    (B : Finset α) (x : α) :
    profile_compatible B (profilePair B x) ∧
    (profilePair B x).1 ⊆ B ∧ (profilePair B x).2 ⊆ B :=
  ⟨profile_compatible_of_point B x, pastProfile_subset B x, futureProfile_subset B x⟩

/-! ## Partial order instance on reconstructedPoints -/

set_option linter.unusedSectionVars false in
@[ext]
theorem reconstructedPoints_ext {B : Finset α} {a b : reconstructedPoints B}
    (h : a.1 = b.1) : a = b :=
  Subtype.ext h

instance reconstructedPoints_partialOrder
    (B : Finset α) : PartialOrder (reconstructedPoints B) where
  le := fun a b => profileLE a.1 b.1
  le_refl := fun a => ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  le_trans := fun a b c hab hbc =>
    ⟨Finset.Subset.trans hab.1 hbc.1, Finset.Subset.trans hbc.2 hab.2⟩
  le_antisymm := fun a b hab hba => by
    apply reconstructedPoints_ext
    exact Prod.ext (Finset.Subset.antisymm hab.1 hba.1) (Finset.Subset.antisymm hba.2 hab.2)

/-- Helper to construct a reconstructed point from a bulk point. -/
def toReconstructed (B : Finset α) (x : α) : reconstructedPoints B :=
  ⟨profilePair B x, profilePair_mem_reconstructed B x⟩

/-
The profile map preserves order.
-/

/-
The profile map is injective under the separation hypothesis.
-/

/-
The profile map strictly preserves order.
-/

/-
The profile map is surjective under interval generation.
-/

/-! ## Main theorems -/

/-
**Theorem 1**: Under separation and order reflection, profilePair is an order embedding
    into compatible profile pairs.
-/

/-
**Theorem 2**: Under interval generation, the profile map is an order isomorphism.
    The bulk IS the boundary profile poset.
-/

/-
**Theorem 3**: Cover relations in α correspond exactly to cover relations in the
    image of the profile map. The backward direction (cover in reconstructedPoints →
    cover in α) holds without interval generation; the full ↔ requires it.
-/

/-
**Theorem 4**: Alexandrov intervals are faithfully reconstructed under the
    full reconstruction hypotheses.
-/


