-- Prove2me | solution 1 for mme_dwz_supported_address_hash_event_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T10:03:31.766207+00:00
-- url     : https://prove2.me/submissions/e62d9f21-175c-4904-99b4-b28565e702de

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

open MME MME.DWZSimultaneous BigOperators
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZHashBudgetInputs

theorem retained_iff_affine {N H p : ℕ} (level : ℕ)
    (reindex : Fin (H + 1) ≃ Fin N) (S : Finset ℕ)
    (a : CoarseAddress N) (state : (Fin (H + 2) → ZMod p) × ZMod p) :
    Retained level reindex S state a ↔
      dwzAsymmetricAffineRetains (level : ZMod p) (S.image (fun n : ℕ ↦ (n : ZMod p)))
        (fieldWord reindex (a 0)) (fieldWord reindex (a 1))
        (fieldWord reindex (a 2)) state := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, h 0, h 1, h 2⟩
  · rintro ⟨s, hs, hx, hy, hz⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨n, hn, ?_⟩
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz

theorem support_bound {N level : ℕ} {a : CoarseAddress N}
    (ha : Supported level a) (i : Fin 3) (t : Fin N) : a i t ≤ level := by
  have h := ha t
  fin_cases i
  · change a 0 t ≤ level
    omega
  · change a 1 t ≤ level
    omega
  · change a 2 t ≤ level
    omega

theorem fieldWord_inj {N H p : ℕ} (reindex : Fin (H + 1) ≃ Fin N)
    {a b : Fin N → ℕ} (ha : ∀ t, a t < p) (hb : ∀ t, b t < p)
    (he : (fieldWord reindex a : Fin (H + 1) → ZMod p) = fieldWord reindex b) :
    a = b := by
  funext t
  have h := congrFun he (reindex.symm t)
  simp only [fieldWord, Equiv.apply_symm_apply] at h
  have hm := (ZMod.natCast_eq_natCast_iff' (a t) (b t) p).mp h
  simpa only [Nat.mod_eq_of_lt (ha t), Nat.mod_eq_of_lt (hb t)] using hm

theorem address_eq_of_xy {N level : ℕ} {a b : CoarseAddress N}
    (ha : Supported level a) (hb : Supported level b)
    (hx : a 0 = b 0) (hy : a 1 = b 1) : a = b := by
  funext i t
  have hax := congrFun hx t
  have hay := congrFun hy t
  have hsa := ha t
  have hsb := hb t
  fin_cases i
  · exact hax
  · exact hay
  · change a 2 t = b 2 t
    omega

theorem address_eq_of_xz {N level : ℕ} {a b : CoarseAddress N}
    (ha : Supported level a) (hb : Supported level b)
    (hx : a 0 = b 0) (hz : a 2 = b 2) : a = b := by
  funext i t
  have hax := congrFun hx t
  have haz := congrFun hz t
  have hsa := ha t
  have hsb := hb t
  fin_cases i
  · exact hax
  · change a 1 t = b 1 t
    omega
  · exact haz

/-- Exact event sizes and all three shared-mode collision bounds for the
literal natural-address retention predicate. -/
theorem supported_address_hash_event_counts
    (N H level p R : ℕ) [Fact p.Prime] (hpodd : Odd p) (hlevel : level < p)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hS : S ⊆ Finset.range p)
    (address : Fin R → CoarseAddress N) (ambient : Finset (Fin R))
    (hsupport : ∀ a ∈ ambient, Supported level (address a))
    (hinjective : Set.InjOn address (ambient : Set (Fin R))) :
    let events := fun a ↦ Finset.univ.filter
      (fun state : (Fin (H + 2) → ZMod p) × ZMod p ↦
        Retained level reindex S state (address a))
    (∀ a state, state ∈ events a ↔ Retained level reindex S state (address a)) ∧
    Fintype.card ((Fin (H + 2) → ZMod p) × ZMod p) = p ^ (H + 3) ∧
    (∀ a ∈ ambient, (events a).card = S.card * p ^ (H + 1)) ∧
    (∀ a ∈ ambient, ∀ b ∈ ambient, a ≠ b →
      (∃ i : Fin 3, address a i = address b i) →
      (events a ∩ events b).card ≤ S.card * p ^ H) := by
  classical
  dsimp only
  let labels : Finset (ZMod p) := S.image (fun n : ℕ ↦ (n : ZMod p))
  have hlabels : labels.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp (hS ha)
    have hb' := Finset.mem_range.mp (hS hb)
    have h := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    simpa only [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using h
  have hevents (a : Fin R) :
      Finset.univ.filter (fun state : (Fin (H + 2) → ZMod p) × ZMod p ↦
          Retained level reindex S state (address a)) =
        dwzAsymmetricAffineStatesRetaining (level : ZMod p) labels
          (fieldWord reindex (address a 0)) (fieldWord reindex (address a 1))
          (fieldWord reindex (address a 2)) := by
    ext state
    simp only [dwzAsymmetricAffineStatesRetaining, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact retained_iff_affine level reindex S (address a) state
  have hfieldSupport (a : Fin R) (ha : a ∈ ambient) (t : Fin (H + 1)) :
      (fieldWord reindex (address a 0) t : ZMod p) +
        fieldWord reindex (address a 1) t + fieldWord reindex (address a 2) t =
          (level : ZMod p) := by
    simpa only [fieldWord, Nat.cast_add] using
      congrArg (fun n : ℕ ↦ (n : ZMod p)) (hsupport a ha (reindex t))
  have hinjField (a : Fin R) (ha : a ∈ ambient) (b : Fin R) (hb : b ∈ ambient)
      (i : Fin 3) :
      (fieldWord reindex (address a i) : Fin (H + 1) → ZMod p) =
          fieldWord reindex (address b i) → address a i = address b i :=
    fieldWord_inj reindex
      (fun t ↦ (support_bound (hsupport a ha) i t).trans_lt hlevel)
      (fun t ↦ (support_bound (hsupport b hb) i t).trans_lt hlevel)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a state
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    exact (pow_succ p (H + 2)).symm
  · intro a ha
    rw [hevents]
    rw [mme_dwz_asymmetric_hash_singleton_fiber_card hpodd
      (level : ZMod p) labels _ _ _ (hfieldSupport a ha), hlabels]
  · intro a ha b hb hab hshared
    rw [hevents, hevents]
    have haddr : address a ≠ address b := fun h ↦ hab (hinjective ha hb h)
    obtain ⟨i, hi⟩ := hshared
    fin_cases i
    · change address a 0 = address b 0 at hi
      have hne : (fieldWord reindex (address a 1) : Fin (H + 1) → ZMod p) ≠
          fieldWord reindex (address b 1) := by
        intro h
        exact haddr (address_eq_of_xy (hsupport a ha) (hsupport b hb) hi
          (hinjField a ha b hb 1 h))
      have h := mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
        (level : ZMod p) labels
        (fieldWord reindex (address a 0)) (fieldWord reindex (address a 1))
        (fieldWord reindex (address a 2)) (fieldWord reindex (address b 0))
        (fieldWord reindex (address b 1)) (fieldWord reindex (address b 2))
        (Or.inl ⟨congrArg (fieldWord reindex) hi, hne⟩)
      simpa only [hlabels] using h
    · change address a 1 = address b 1 at hi
      have hne : (fieldWord reindex (address a 0) : Fin (H + 1) → ZMod p) ≠
          fieldWord reindex (address b 0) := by
        intro h
        exact haddr (address_eq_of_xy (hsupport a ha) (hsupport b hb)
          (hinjField a ha b hb 0 h) hi)
      have h := mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
        (level : ZMod p) labels
        (fieldWord reindex (address a 0)) (fieldWord reindex (address a 1))
        (fieldWord reindex (address a 2)) (fieldWord reindex (address b 0))
        (fieldWord reindex (address b 1)) (fieldWord reindex (address b 2))
        (Or.inr ⟨congrArg (fieldWord reindex) hi, hne⟩)
      simpa only [hlabels] using h
    · change address a 2 = address b 2 at hi
      have hne : (fieldWord reindex (address a 0) : Fin (H + 1) → ZMod p) ≠
          fieldWord reindex (address b 0) := by
        intro h
        exact haddr (address_eq_of_xz (hsupport a ha) (hsupport b hb)
          (hinjField a ha b hb 0 h) hi)
      have h := mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
        (level : ZMod p) labels
        (fieldWord reindex (address a 0)) (fieldWord reindex (address a 1))
        (fieldWord reindex (address a 2)) (fieldWord reindex (address b 0))
        (fieldWord reindex (address b 1)) hne
      rw [hi] at h
      simpa only [hlabels, hi] using h

end MME.DWZHashBudgetInputs

theorem solution
    (N H level p R : ℕ) [Fact p.Prime] (hpodd : Odd p) (hlevel : level < p)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hS : S ⊆ Finset.range p)
    (address : Fin R → CoarseAddress N) (ambient : Finset (Fin R))
    (hsupport : ∀ a ∈ ambient, Supported level (address a))
    (hinjective : Set.InjOn address (ambient : Set (Fin R))) :
    let events := fun a ↦ Finset.univ.filter
      (fun state : (Fin (H + 2) → ZMod p) × ZMod p ↦
        Retained level reindex S state (address a))
    (∀ a state, state ∈ events a ↔ Retained level reindex S state (address a)) ∧
    Fintype.card ((Fin (H + 2) → ZMod p) × ZMod p) = p ^ (H + 3) ∧
    (∀ a ∈ ambient, (events a).card = S.card * p ^ (H + 1)) ∧
    (∀ a ∈ ambient, ∀ b ∈ ambient, a ≠ b →
      (∃ i : Fin 3, address a i = address b i) →
      (events a ∩ events b).card ≤ S.card * p ^ H) := by
  exact MME.DWZHashBudgetInputs.supported_address_hash_event_counts
    N H level p R hpodd hlevel reindex S hS address ambient hsupport hinjective

