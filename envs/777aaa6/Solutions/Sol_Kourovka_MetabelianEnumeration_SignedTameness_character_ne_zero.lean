-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SignedTameness.character_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:46.503209+00:00
-- url     : https://prove2.me/submissions/e449a1c6-bad3-40b0-97a1-778a58fab950

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Modules_SignedTameness

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
namespace Kourovka.MetabelianEnumeration.SignedTameness
theorem _root_.solution {k : ℕ} {x : Fin k → ℝ} (hx : x ≠ 0) : character x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := DFunLike.congr_fun h (Pi.single i 1)
  simpa [character, Pi.single_apply, mul_ite] using hi
end Kourovka.MetabelianEnumeration.SignedTameness
