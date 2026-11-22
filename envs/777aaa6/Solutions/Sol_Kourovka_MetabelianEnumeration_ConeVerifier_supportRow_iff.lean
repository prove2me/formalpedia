-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.supportRow_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:59.806297+00:00
-- url     : https://prove2.me/submissions/0d51c78d-3f96-4255-b7b1-c43f3cad298c

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (u : Vec n) (epsilon : ℚ) (x : Fin n → ℝ) :
    (supportRow u epsilon).eval x ≤ 0 ↔ dot u x ≤ epsilon := by
  simp only [supportRow, Row.eval, Rat.cast_neg, dot]
  constructor <;> intro h <;> linarith
end Kourovka.MetabelianEnumeration.ConeVerifier
