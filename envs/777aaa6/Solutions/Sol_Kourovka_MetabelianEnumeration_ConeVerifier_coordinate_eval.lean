-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.coordinate_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:27.268183+00:00
-- url     : https://prove2.me/submissions/d2597916-46ef-4034-b0b7-5c9a074812d9

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (i : Fin n) (a b : ℚ) (x : Fin n → ℝ) :
    (coordinate i a b).eval x = (a : ℝ) * x i + b := by
  simp [coordinate, Row.eval, apply_ite, ite_mul]
end Kourovka.MetabelianEnumeration.ConeVerifier
