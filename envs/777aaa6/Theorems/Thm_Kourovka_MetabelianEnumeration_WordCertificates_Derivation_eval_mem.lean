-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_Derivation_eval_mem
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.Derivation.eval_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:38.279614+00:00
-- url     : https://prove2.me/theorems/6573bfe9-9965-4130-b2f2-f642d009ca45
-- title:
--   Derivation: eval mem
-- statement:
--   The Derivation construction uses the eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L36-L47
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L36-L47

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.Derivation.eval_mem {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (d : Derivation n) : d.eval rels ∈ Subgroup.normalClosure {r | r ∈ rels} := by sorry
