-- Prove2me | solution 1 for mme_dwz_claim6_8_concrete_bounded_address_survival
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:20:45.965484+00:00
-- url     : https://prove2.me/submissions/4ee0cb2a-2323-4e37-be13-9f23e2212ee7

import Mathlib
import Theorems.Thm_mme_dwz_lemma3_11_bounded_address_collision_fiber
import Theorems.Thm_mme_dwz_claim6_8_one_eighth_from_collision_budget

open BigOperators
set_option autoImplicit false

/-! The concrete finite collision part of DWZ Claim 6.8 for bounded natural
addresses.  All candidates are already the compatible competitors; only their
source-specific count and the corresponding modulus lower bound remain. -/

theorem solution
    {p n levelSum : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (I K : Fin (n + 1) → Fin (levelSum + 1))
    (candidates : Finset (Fin (n + 1) → Fin (levelSum + 1)))
    (hdistinct : ∀ A ∈ candidates, A ≠ I)
    (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad] :
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w A => b0 + ∑ t, ((A t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w0 w C =>
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t,
            ((levelSum : ZMod p) - (C t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w =>
        2 * (∑ t, ((I t).val : ZMod p) * w t) -
          ∑ t, ((levelSum : ZMod p) - (K t).val) * w t
    (∀ w, bad w →
      ∃ A ∈ candidates, hX w A = hZ (conditionedW0 w) w K) →
    8 * candidates.card ≤ p →
    8 * (Finset.univ.filter bad).card ≤
      Fintype.card (Fin (n + 1) → ZMod p) := by
  dsimp only
  intro hbad hbudget
  let collides :
      (Fin (n + 1) → Fin (levelSum + 1)) →
      (Fin (n + 1) → ZMod p) → Prop :=
    fun A w =>
      b0 + ∑ t, ((A t).val : ZMod p) * w t =
        b0 + (2 : ZMod p)⁻¹ *
          ((2 * (∑ t, ((I t).val : ZMod p) * w t) -
              ∑ t, ((levelSum : ZMod p) - (K t).val) * w t) +
            ∑ t, ((levelSum : ZMod p) - (K t).val) * w t)
  apply mme_dwz_claim6_8_one_eighth_from_collision_budget
    candidates (fun _ => True) collides bad p
      (Nat.Prime.pos (Fact.out : p.Prime))
  · intro w hw
    obtain ⟨A, hA, hAw⟩ := hbad w hw
    exact ⟨A, hA, trivial, hAw⟩
  · intro A hA _
    have hfiber :=
      (mme_dwz_lemma3_11_bounded_address_collision_fiber
        hpodd hlevel b0 I A K (Ne.symm (hdistinct A hA))).2
    exact hfiber.le
  · simpa using hbudget
