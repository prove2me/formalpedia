-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.cubeSphere_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:47:11.713177+00:00
-- url     : https://prove2.me/submissions/031944d1-d53e-4d9d-b961-27c1dae8d1de

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} {x : Fin n → ℝ} (hx : CubeSphere x) : x ≠ 0 := by
  obtain ⟨i, hi⟩ := hx.2
  intro h
  simp only [h, Pi.zero_apply] at hi
  rcases hi with hi | hi <;> linarith
end Kourovka.MetabelianEnumeration.ConeVerifier
