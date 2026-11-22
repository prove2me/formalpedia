-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.coneCover_iff_cubeMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:32.4521+00:00
-- url     : https://prove2.me/submissions/13fa9988-46c4-4366-bd49-7a3534ff64e4

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_cubeSphere_ne_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_normalize_to_cube
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_dot_div

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) :
    ConeCover supports ↔ CubeMargin supports 0 := by
  constructor
  · intro h x hx
    simpa only [Rat.cast_zero] using h x (cubeSphere_ne_zero hx)
  · intro h x hx
    obtain ⟨c, hc, hx'⟩ := normalize_to_cube x hx
    obtain ⟨s, hs, hpos⟩ := h _ hx'
    refine ⟨s, hs, ?_⟩
    intro u hu
    have hp := hpos u hu
    rw [Rat.cast_zero, dot_div] at hp
    exact (div_pos_iff_of_pos_right hc).mp hp
end Kourovka.MetabelianEnumeration.ConeVerifier
