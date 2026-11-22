-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.designated_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:45.564182+00:00
-- url     : https://prove2.me/submissions/1e4a01e2-2ae6-4daa-8b68-9fff870f77bd

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_alphabet_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec (fun p : DatumCode × (ℕ × ℕ) => designated p.1 p.2.1 p.2.2) :=
  Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp
      ((Primrec.list_getD []).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
    (alphabet_primrec.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableCoverWords
