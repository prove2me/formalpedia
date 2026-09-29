-- Prove2me | solution 1 for cover_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:31.068271+00:00
-- url     : https://prove2.me/submissions/a52d41e1-6fd7-466e-9555-b4889db47a3a

-- Sol generated from Bridges/CausalHolography.lean
import Mathlib
import Definitions.Def_Bridges_CausalHolography
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



variable {α : Type*} [PartialOrder α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]












/-! ## Helper lemmas -/

variable {α : Type*} [PartialOrder α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]








/-! ## Partial order instance on reconstructedPoints -/




/-
The profile map preserves order.
-/
theorem toReconstructed_le_iff
    (B : Finset α)
    (hreflect :
      ∀ x y : α,
        x ≤ y ↔
          pastProfile B x ⊆ pastProfile B y ∧
          futureProfile B y ⊆ futureProfile B x)
    (x y : α) :
    toReconstructed B x ≤ toReconstructed B y ↔ x ≤ y := by
  exact iff_comm.mp (hreflect x y)

/-
The profile map is injective under the separation hypothesis.
-/

/-
The profile map strictly preserves order.
-/
theorem toReconstructed_lt_iff
    (B : Finset α)
    (_hsep : separates_bulk B)
    (hreflect :
      ∀ x y : α,
        x ≤ y ↔
          pastProfile B x ⊆ pastProfile B y ∧
          futureProfile B y ⊆ futureProfile B x)
    (x y : α) :
    toReconstructed B x < toReconstructed B y ↔ x < y := by
  rw [ lt_iff_le_not_ge, lt_iff_le_not_ge ];
  -- Apply the toReconstructed_le_iff theorem to both parts of the conjunction.
  simp [toReconstructed_le_iff B hreflect]

/-
The profile map is surjective under interval generation.
-/
theorem toReconstructed_surjective
    (B : Finset α) (hgen : interval_generated B) :
    Function.Surjective (toReconstructed B) := by
  intro q
  obtain ⟨x, hx⟩ := hgen q.1 q.2.1 q.2.2.1 q.2.2.2
  use x
  simp [hx, toReconstructed]

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

theorem solution    [Finite α]
    (B : Finset α)
    (hsep : separates_bulk B)
    (hgen : interval_generated B)
    (hreflect :
      ∀ x y : α,
        x ≤ y ↔
          pastProfile B x ⊆ pastProfile B y ∧
          futureProfile B y ⊆ futureProfile B x) :
    ∀ x y : α,
      isCoverRel x y ↔
        isCoverRel (toReconstructed B x) (toReconstructed B y) := by
  intro x y;
  constructor;
  · rintro ⟨ hxy, h ⟩;
    refine' ⟨ _, _ ⟩;
    · exact toReconstructed_lt_iff B hsep hreflect x y |>.2 hxy;
    · contrapose! h;
      obtain ⟨ z, hz₁, hz₂ ⟩ := h;
      obtain ⟨ w, hw ⟩ := toReconstructed_surjective B hgen z;
      exact ⟨ w, by simpa [ hw ] using toReconstructed_lt_iff B hsep hreflect x w |>.1 ( by simpa [ hw ] using hz₁ ), by simpa [ hw ] using toReconstructed_lt_iff B hsep hreflect w y |>.1 ( by simpa [ hw ] using hz₂ ) ⟩;
  · intro h;
    constructor;
    · exact toReconstructed_lt_iff B hsep hreflect x y |>.1 h.1;
    · rintro ⟨ z, hxz, hzy ⟩;
      have hz : toReconstructed B x < toReconstructed B z ∧ toReconstructed B z < toReconstructed B y := by
        exact ⟨ toReconstructed_lt_iff B hsep hreflect x z |>.2 hxz, toReconstructed_lt_iff B hsep hreflect z y |>.2 hzy ⟩;
      exact h.2 ⟨ toReconstructed B z, hz.1, hz.2 ⟩
