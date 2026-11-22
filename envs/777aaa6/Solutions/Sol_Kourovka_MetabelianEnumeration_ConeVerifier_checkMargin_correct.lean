-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.checkMargin_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:38.525425+00:00
-- url     : https://prove2.me/submissions/3f368bb8-7aba-4060-958f-0cf719330d57

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_badDirection_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    checkMargin supports epsilon = true ↔ CubeMargin supports epsilon := by
  rw [checkMargin, Bool.not_eq_true']
  rw [← Bool.not_eq_true, badDirection_correct]
  constructor
  · intro h x hx
    by_contra hn
    push_neg at hn
    exact h ⟨x, hx, hn⟩
  · intro h
    rintro ⟨x, hx, hn⟩
    obtain ⟨s, hs, hpos⟩ := h x hx
    obtain ⟨u, hu, hle⟩ := hn s hs
    exact (not_lt_of_ge hle) (hpos u hu)
end Kourovka.MetabelianEnumeration.ConeVerifier
