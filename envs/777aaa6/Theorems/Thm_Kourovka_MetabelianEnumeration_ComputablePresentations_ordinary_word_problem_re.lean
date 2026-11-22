-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_ordinary_word_problem_re
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.ordinary_word_problem_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:30.645053+00:00
-- url     : https://prove2.me/theorems/dd75c7ed-c4c7-4fea-af6a-cb1cbd51730d
-- title:
--   Computable Presentations: ordinary word problem re
-- statement:
--   An unconditional uniform semidecision procedure, on the original presentation
--   and word codes, for equality to the identity in their ordinary presented group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L131-L141
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L131-L141

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.ordinary_word_problem_re :
    REPred (fun input : PresentationCode × List (ℕ × Bool) =>
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1) := by sorry
