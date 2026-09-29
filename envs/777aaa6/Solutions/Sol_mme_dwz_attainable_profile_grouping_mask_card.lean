-- Prove2me | solution 1 for mme_dwz_attainable_profile_grouping_mask_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:10:43.040278+00:00
-- url     : https://prove2.me/submissions/e6fc804f-3a0d-464a-b56e-9c87693c57b9

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

open scoped Classical

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZProfileTransport

/-- Exact component multiplicities produce a component-preserving position
equivalence; no availability of letters is used in this positional step. -/
theorem exists_positions_of_fiber_card
    {P C : Type*} [Fintype P]
    (cell : P → C) (n : C → ℕ)
    (hcount : ∀ c, Fintype.card {p : P // cell p = c} = n c) :
    ∃ positions : P ≃ Σ c, Fin (n c),
      ∀ c r, cell (positions.symm ⟨c, r⟩) = c := by
  classical
  let fiber (c : C) : {p : P // cell p = c} ≃ Fin (n c) :=
    Fintype.equivFinOfCardEq (hcount c)
  let positions := (Equiv.sigmaFiberEquiv cell).symm.trans
    (Equiv.sigmaCongrRight fiber)
  refine ⟨positions, ?_⟩
  intro c r
  exact (fiber c |>.symm r).property

/-- A fiber count is unchanged by grouping positions, with their original
component labels. The condition may depend on the entire original position. -/
theorem grouped_fiber_card
    {P C : Type*} [Fintype P]
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (Q : P → Prop) (c : C) :
    Fintype.card {p : P // cell p = c ∧ Q p} =
      Fintype.card {r : Fin (n c) // Q (positions.symm ⟨c, r⟩)} := by
  classical
  let f : {r : Fin (n c) // Q (positions.symm ⟨c, r⟩)} →
      {p : P // cell p = c ∧ Q p} :=
    fun r ↦ ⟨positions.symm ⟨c, r.val⟩, hcell c r.val, r.property⟩
  symm
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro r s hrs
    apply Subtype.ext
    have hs : (⟨c, r.val⟩ : Σ c, Fin (n c)) = ⟨c, s.val⟩ :=
      positions.symm.injective (congrArg Subtype.val hrs)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  · intro p
    obtain ⟨⟨c', r⟩, hr⟩ := positions.symm.surjective p.val
    have hc : c' = c := (hcell c' r).symm.trans
      (by rw [hr]; exact p.property.1)
    subst c'
    refine ⟨⟨r, ?_⟩, ?_⟩
    · simpa only [hr] using p.property.2
    · apply Subtype.ext
      exact hr

/-- Componentwise exact histograms are precisely the grouped-word histograms. -/
theorem grouped_profile_iff
    {P C A W : Type*} [Fintype P]
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (tag : C → A → W) (mu : C → W → ℕ) (f : P → A) :
    (∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w) ↔
      ∀ c w, Fintype.card {r : Fin (n c) //
        tag c (f (positions.symm ⟨c, r⟩)) = w} = mu c w := by
  simp_rw [grouped_fiber_card cell n positions hcell]

/-- Pointwise admissibility also transports, including empty component fibers. -/
theorem grouped_allowed_iff
    {P C A : Type*} (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (allowed : C → A → Prop) (f : P → A) :
    (∀ p, allowed (cell p) (f p)) ↔
      ∀ c r, allowed c (f (positions.symm ⟨c, r⟩)) := by
  constructor
  · intro h c r
    simpa only [hcell] using h (positions.symm ⟨c, r⟩)
  · intro h p
    have hc : cell p = (positions p).1 := by
      simpa only [positions.symm_apply_apply] using
        hcell (positions p).1 (positions p).2
    rw [hc]
    simpa only [positions.symm_apply_apply] using h (positions p).1 (positions p).2

/-- The full profile router is a bijection, not a count comparison. Its action
is the same grouped-word action as the tensor-power regrouping theorem. -/
theorem exists_grouped_profile_equiv
    {P C A W : Type*} [Fintype P]
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (allowed : C → A → Prop) (tag : C → A → W) (mu : C → W → ℕ) :
    ∃ E : {f : P → A //
        (∀ p, allowed (cell p) (f p)) ∧
        ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w} ≃
      ((c : C) → {g : Fin (n c) → A //
        (∀ r, allowed c (g r)) ∧
        ∀ w, Fintype.card {r : Fin (n c) // tag c (g r) = w} = mu c w}),
      ∀ f c r, (E f c).val r = f.val (positions.symm ⟨c, r⟩) := by
  classical
  let group : (P → A) ≃ ((c : C) → Fin (n c) → A) :=
    (Equiv.arrowCongr positions (Equiv.refl A)).trans
      (Equiv.piCurry (fun (c : C) (_ : Fin (n c)) ↦ A))
  have hprop (f : P → A) :
      ((∀ p, allowed (cell p) (f p)) ∧
        ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w) ↔
      ∀ c, (∀ r, allowed c (group f c r)) ∧
        ∀ w, Fintype.card {r : Fin (n c) // tag c (group f c r) = w} = mu c w := by
    change _ ↔ ∀ c, (∀ r, allowed c (f (positions.symm ⟨c, r⟩))) ∧
      ∀ w, Fintype.card {r : Fin (n c) //
        tag c (f (positions.symm ⟨c, r⟩)) = w} = mu c w
    rw [grouped_allowed_iff cell n positions hcell,
      grouped_profile_iff cell n positions hcell]
    constructor
    · exact fun h c ↦ ⟨h.1 c, h.2 c⟩
    · exact fun h ↦ ⟨fun c ↦ (h c).1, fun c ↦ (h c).2⟩
  let E₀ := group.subtypeEquiv
    (p := fun f ↦ (∀ p, allowed (cell p) (f p)) ∧
      ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w)
    (q := fun g ↦ ∀ c, (∀ r, allowed c (g c r)) ∧
      ∀ w, Fintype.card {r : Fin (n c) // tag c (g c r) = w} = mu c w) hprop
  let E := E₀.trans (Equiv.subtypePiEquivPi
    (β := fun c : C ↦ Fin (n c) → A)
    (p := fun c g ↦ (∀ r, allowed c (g r)) ∧
      ∀ w, Fintype.card {r : Fin (n c) // tag c (g r) = w} = mu c w))
  exact ⟨E, fun _ _ _ ↦ rfl⟩

/-- Any hole mask transports exactly along a block-index equivalence. No
injectivity is asserted for the separate atomic-basis-to-block label. -/
theorem mask_card_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X ≃ Y) (mask : X → Prop) :
    Fintype.card {x : X // mask x} =
      Fintype.card {y : Y // mask (E.symm y)} := by
  classical
  exact Fintype.card_congr
    (E.subtypeEquiv (fun x ↦ by simp only [E.symm_apply_apply]))

/-- Attainability is the actual image of the allowed index fibers. Pointwise
attainability is equivalent to a genuine, possibly nonunique basis-word lift. -/
theorem attainable_word_iff_lift
    {P C A : Type*} {I : C → Type*}
    (cell : P → C) (good : (c : C) → I c → Prop)
    (label : (c : C) → I c → A) (f : P → A) :
    (∀ p, ∃ a : I (cell p), good (cell p) a ∧ label (cell p) a = f p) ↔
      ∃ a : (p : P) → I (cell p),
        (∀ p, good (cell p) (a p)) ∧ ∀ p, label (cell p) (a p) = f p := by
  classical
  constructor
  · intro h
    exact ⟨fun p ↦ Classical.choose (h p),
      fun p ↦ (Classical.choose_spec (h p)).1,
      fun p ↦ (Classical.choose_spec (h p)).2⟩
  · rintro ⟨a, hg, hl⟩ p
    exact ⟨a p, hg p, hl p⟩

/-- An empty component carries its one empty word exactly when all demanded
counts vanish. Admissibility is vacuous, even if its basis alphabet is empty. -/
theorem empty_component_profile_iff
    {A W : Type*} (allowed : A → Prop) (tag : A → W)
    (mu : W → ℕ) (f : Fin 0 → A) :
    ((∀ r, allowed (f r)) ∧
      ∀ w, Fintype.card {r : Fin 0 // tag (f r) = w} = mu w) ↔
      ∀ w, mu w = 0 := by
  simp [eq_comm]

/-- The useful block universe is the actual image of the allowed local basis
indices, with exact profiles imposed. The router is bijective on these blocks
and preserves every pulled-back mask cardinality. It does not count basis
words, and it does not assert that a demanded profile has any realizations. -/
theorem attainable_profile_factorization
    {P C A W : Type*} [Fintype P] [Fintype C] [Fintype A]
    {I : C → Type*}
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (good : (c : C) → I c → Prop) (label : (c : C) → I c → A)
    (tag : C → A → W) (mu : C → W → ℕ) :
    let Global := {f : P → A //
      (∀ p, ∃ a : I (cell p), good (cell p) a ∧ label (cell p) a = f p) ∧
      ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w}
    let Grouped := (c : C) → {g : Fin (n c) → A //
      (∀ r, ∃ a : I c, good c a ∧ label c a = g r) ∧
      ∀ w, Fintype.card {r : Fin (n c) // tag c (g r) = w} = mu c w}
    ∃ E : Global ≃ Grouped,
      (∀ f c r, (E f c).val r = f.val (positions.symm ⟨c, r⟩)) ∧
      (∀ f : Global, ∃ a : (p : P) → I (cell p),
        (∀ p, good (cell p) (a p)) ∧ ∀ p, label (cell p) (a p) = f.val p) ∧
      ∀ mask : Global → Prop,
        Fintype.card {f : Global // mask f} =
          Fintype.card {g : Grouped // mask (E.symm g)} := by
  classical
  dsimp only
  obtain ⟨E, hE⟩ := exists_grouped_profile_equiv cell n positions hcell
    (fun c a ↦ ∃ i : I c, good c i ∧ label c i = a) tag mu
  refine ⟨E, hE, ?_, ?_⟩
  · intro f
    exact (attainable_word_iff_lift cell good label f.val).mp f.property.1
  · intro mask
    exact mask_card_eq E mask

theorem empty_component_profile_card
    {A W : Type*} [Fintype A]
    (allowed : A → Prop) (tag : A → W) (mu : W → ℕ) :
    Fintype.card {f : Fin 0 → A // (∀ r, allowed (f r)) ∧
      ∀ w, Fintype.card {r : Fin 0 // tag (f r) = w} = mu w} =
      if (∀ w, mu w = 0) then 1 else 0 := by
  classical
  simp_rw [empty_component_profile_iff]
  split_ifs with h
  · simp [h]
  · simp [h]

end MME.DWZProfileTransport

theorem solution
    {P C A W : Type*} [Fintype P] [Fintype C] [Fintype A]
    {I : C → Type*}
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (good : (c : C) → I c → Prop) (label : (c : C) → I c → A)
    (tag : C → A → W) (mu : C → W → ℕ) :
    let Global := {f : P → A //
      (∀ p, ∃ a : I (cell p), good (cell p) a ∧ label (cell p) a = f p) ∧
      ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w}
    let Grouped := (c : C) → {g : Fin (n c) → A //
      (∀ r, ∃ a : I c, good c a ∧ label c a = g r) ∧
      ∀ w, Fintype.card {r : Fin (n c) // tag c (g r) = w} = mu c w}
    ∃ E : Global ≃ Grouped,
      (∀ f c r, (E f c).val r = f.val (positions.symm ⟨c, r⟩)) ∧
      (∀ f : Global, ∃ a : (p : P) → I (cell p),
        (∀ p, good (cell p) (a p)) ∧ ∀ p, label (cell p) (a p) = f.val p) ∧
      ∀ mask : Global → Prop,
        Fintype.card {f : Global // mask f} =
          Fintype.card {g : Grouped // mask (E.symm g)} := by
  exact MME.DWZProfileTransport.attainable_profile_factorization
    cell n positions hcell good label tag mu

