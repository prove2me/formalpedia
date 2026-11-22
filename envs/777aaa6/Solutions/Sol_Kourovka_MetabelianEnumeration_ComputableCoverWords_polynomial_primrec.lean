-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomial_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:57.340756+00:00
-- url     : https://prove2.me/submissions/c88e40e8-da5a-4dec-b8eb-5c969c1786fc

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_zpow_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_prod_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_conjugate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_ordered_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_conjugate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec (fun p : (ℕ × WordGroup) × PolynomialCode =>
    polynomial p.1.1 p.1.2 p.2) :=
  prod_primrec.comp (Primrec.list_map (Primrec.snd.comp Primrec.snd)
    (conjugate_primrec.comp
      (zpow_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (ordered_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (ComputableWords.inv_primrec.comp
          (ordered_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))))).to₂)
end Kourovka.MetabelianEnumeration.ComputableCoverWords
