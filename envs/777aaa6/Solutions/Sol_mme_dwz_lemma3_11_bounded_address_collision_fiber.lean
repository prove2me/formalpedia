-- Prove2me | solution 1 for mme_dwz_lemma3_11_bounded_address_collision_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:12:10.63734+00:00
-- url     : https://prove2.me/submissions/a89cb2bd-8095-404b-8f36-71ad976412a0

import Mathlib
import Theorems.Thm_mme_dwz_lemma3_11_fixed_z_collision_fiber

open BigOperators

set_option autoImplicit false

theorem solution
    {p n levelSum : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (I I' K : Fin (n + 1) → Fin (levelSum + 1)) (hII' : I ≠ I') :
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
    (∀ w w0, hX w I = hZ w0 w K ↔ w0 = conditionedW0 w) ∧
      p * ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod p =>
          hX w I' = hZ (conditionedW0 w) w K)).card) =
        Fintype.card (Fin (n + 1) → ZMod p) := by
  dsimp only
  let castWord : (Fin (n + 1) → Fin (levelSum + 1)) →
      (Fin (n + 1) → ZMod p) :=
    fun A t => ((A t).val : ZMod p)
  have hcast : Function.Injective castWord := by
    intro A B hAB
    funext t
    apply Fin.ext
    have hcoord : ((A t).val : ZMod p) = ((B t).val : ZMod p) :=
      congrFun hAB t
    have hval := congrArg ZMod.val hcoord
    have hAlt : (A t).val < p := by omega
    have hBlt : (B t).val < p := by omega
    simpa [ZMod.val_natCast_of_lt hAlt,
      ZMod.val_natCast_of_lt hBlt] using hval
  have hmodne : castWord I ≠ castWord I' := by
    exact fun h => hII' (hcast h)
  simpa only [castWord] using
    (mme_dwz_lemma3_11_fixed_z_collision_fiber
      hpodd (levelSum : ZMod p) b0
      (castWord I) (castWord I') (castWord K) hmodne)
