-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.badDirection_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:03.454338+00:00
-- url     : https://prove2.me/submissions/4481dd9f-b266-4cc6-af61-913eba260ab0

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_any_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_faceRows_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_choices_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
set_option maxHeartbeats 2000000
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec₂ badDirection := by
  let Base := (ℕ × ℕ) × SupportsCode
  let Face := (Base × ℕ) × ℤ
  have hn : Primrec (fun p : Face => p.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hi : Primrec (fun p : Face => p.1.2) := Primrec.snd.comp Primrec.fst
  have hf : Primrec (fun p : Face => faceRows p.1.1.1.1 p.1.2 p.2) :=
    faceRows_primrec.comp ((hn.pair hi).pair Primrec.snd)
  have hc : Primrec (fun p : Face × List RowCode =>
      ComputableFourierMotzkin.check p.1.1.1.1.1 (p.2 ++ faceRows p.1.1.1.1.1 p.1.1.2 p.1.2)) :=
    ComputableFourierMotzkin.check_primrec.comp (hn.comp Primrec.fst)
      (Primrec.list_append.comp Primrec.snd (hf.comp Primrec.fst))
  have hs : Primrec (fun p : Face => choices p.1.1.1.2 p.1.1.2) :=
    choices_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hrows : Primrec (fun p : Face => (choices p.1.1.1.2 p.1.1.2).any fun rows =>
      ComputableFourierMotzkin.check p.1.1.1.1 (rows ++ faceRows p.1.1.1.1 p.1.2 p.2)) :=
    any_primrec hs hc.to₂
  have hsign : Primrec (fun p : Base × ℕ => ([-1, 1] : List ℤ).any fun sign =>
      (choices p.1.1.2 p.1.2).any fun rows =>
        ComputableFourierMotzkin.check p.1.1.1 (rows ++ faceRows p.1.1.1 p.2 sign)) :=
    any_primrec (Primrec.const [-1, 1]) hrows.to₂
  exact any_primrec (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) hsign.to₂
end Kourovka.MetabelianEnumeration.ComputableCone
