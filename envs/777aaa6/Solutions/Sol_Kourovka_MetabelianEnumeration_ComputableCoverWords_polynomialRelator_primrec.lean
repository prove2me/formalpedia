-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelator_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:39.273656+00:00
-- url     : https://prove2.me/submissions/91d2e993-add1-4051-912e-7749c43f7f60

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_of_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomial_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
set_option maxHeartbeats 1000000
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec polynomialRelator := by
  have hx : Primrec (fun p : (DatumCode × ℕ) × PolynomialCode =>
      (FreeGroup.of (dimension p.1.1 + p.1.2) : WordGroup)) :=
    of_primrec.comp (Primrec.nat_add.comp
      (dimension_primrec.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
  exact ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp hx)
    (polynomial_primrec.comp
      (((dimension_primrec.comp (Primrec.fst.comp Primrec.fst)).pair hx).pair Primrec.snd))
end Kourovka.MetabelianEnumeration.ComputableCoverWords
