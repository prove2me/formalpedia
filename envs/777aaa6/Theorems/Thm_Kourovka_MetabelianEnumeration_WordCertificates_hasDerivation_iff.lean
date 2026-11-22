-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_hasDerivation_iff
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.hasDerivation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:45.114497+00:00
-- url     : https://prove2.me/theorems/4bc0b488-b1b5-4870-894c-639043b0e136
-- title:
--   Word Certificates: has Derivation iff
-- statement:
--   The Word Certificates construction uses the has Derivation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L75-L82
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L75-L82

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.hasDerivation_iff {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (r : FreeGroup (Fin n)) :
    (∃ d : Derivation n, d.eval rels = r) ↔ r ∈ Subgroup.normalClosure {r | r ∈ rels} := by sorry
