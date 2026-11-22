-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.wordEq_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:04.15268+00:00
-- url     : https://prove2.me/submissions/2db796be-9f1e-438a-994c-b507a59a8547

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
omit [Primcodable α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution (left right : List (α × Bool)) :
    wordEq left right = true ↔ FreeGroup.mk left = FreeGroup.mk right := by
  simp only [wordEq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg FreeGroup.mk h
    simpa only [FreeGroup.reduce.self] using h'
  · intro h
    have h' := congrArg FreeGroup.toWord h
    simpa only [FreeGroup.toWord_mk] using h'
end Kourovka.MetabelianEnumeration.ComputableWords
