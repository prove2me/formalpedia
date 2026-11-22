-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_checkWord_correct
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.checkWord_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:19.986863+00:00
-- url     : https://prove2.me/theorems/5ec2859b-8f2b-4a7d-8d2d-2b75a273e36e
-- title:
--   Word Certificates: check Word correct
-- statement:
--   Every trivial word has a finite accepted certificate, and accepted certificates
--   always certify actual triviality in the ordinary presented group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L89-L93
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L89-L93

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.checkWord_correct {n : ℕ} (rels : List (FreeGroup (Fin n))) (w : Word n) :
    (∃ d, checkWord rels w d = true) ↔
      PresentedGroup.mk {r | r ∈ rels} (FreeGroup.mk w) = 1 := by sorry
