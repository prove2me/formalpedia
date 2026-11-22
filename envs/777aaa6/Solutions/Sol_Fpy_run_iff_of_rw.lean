-- Prove2me | solution 1 for Fpy.run_iff_of_rw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:04:08.494381+00:00
-- url     : https://prove2.me/submissions/42002803-a249-4a7e-909e-96b23edb09e7

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
import Theorems.Thm_Fpy_Rw_sim

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}
namespace Fpy
theorem _root_.solution (hA : A.Sound Φ) {f : Fn} {y : Var} {s s' : Stmt L} {a : AVal D}
    (hΦ : Φ f = some (y, s)) (hΦ' : Φ' f = some (y, s'))
    (h : Rw A Φ Φ' X (.single y a) (some .real) s s') {v v' : Val} (hv : Describes a v) :
    Run Φ f v v' ↔ Run Φ' f v v' := by
  have hsim := h.sim hA (AEnv.holds_single hv) (Store.Agree.refl _) (admits_some _)
  constructor
  · rintro ⟨_, _, hΦ₁, hs⟩
    rw [hΦ] at hΦ₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
    obtain ⟨_, hs', hag⟩ := hsim.1 _ hs
    obtain rfl := hag.ret_left
    exact ⟨y, s', hΦ', hs'⟩
  · rintro ⟨_, _, hΦ₁, hs'⟩
    rw [hΦ'] at hΦ₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
    obtain ⟨_, hs, hag⟩ := hsim.2 _ hs'
    obtain rfl := hag.ret_right
    exact ⟨y, s, hΦ, hs⟩
end Fpy
