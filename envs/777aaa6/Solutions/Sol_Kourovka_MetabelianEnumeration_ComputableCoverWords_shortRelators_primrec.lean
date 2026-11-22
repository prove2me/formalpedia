-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:36.297064+00:00
-- url     : https://prove2.me/submissions/ca316557-7b41-4dbf-bf92-e7080404d080

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_shortRelator_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_alphabet_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_ball_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec₂ shortRelators := by
  let Base := DatumCode × ℕ
  have hball : Primrec (fun p : (Base × ℕ) × ℕ =>
      ComputableLatticeBall.ball (dimension p.1.1.1) p.1.1.2) :=
    ComputableLatticeBall.ball_primrec.comp
      (dimension_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec (fun p : ((Base × ℕ) × ℕ) × List ℤ =>
      shortRelator (p.1.1.1.1, ((p.1.1.2, p.1.2), p.2))) :=
    shortRelator_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have hv := Primrec.list_map hball hrow.to₂
  have hj := Primrec.list_flatMap
    (Primrec.list_range.comp (alphabet_primrec.comp (Primrec.fst.comp Primrec.fst))) hv.to₂
  exact Primrec.list_flatMap (Primrec.list_range.comp (alphabet_primrec.comp Primrec.fst)) hj.to₂
end Kourovka.MetabelianEnumeration.ComputableCoverWords
