-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.dot_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:32.605182+00:00
-- url     : https://prove2.me/submissions/1492df7b-ecdb-4bb0-a4e1-f816bb4d64d2

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (u : Vec n) (x : Fin n → ℝ) (c : ℝ) :
    dot u (fun i => x i / c) = dot u x / c := by
  simp only [dot, mul_div_assoc, Finset.sum_div]
end Kourovka.MetabelianEnumeration.ConeVerifier
