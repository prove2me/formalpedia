-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_presented_word_problem_re
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.presented_word_problem_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:21.572213+00:00
-- url     : https://prove2.me/theorems/85efc484-766e-43b4-99a1-6dbc77857741
-- title:
--   Computable Closure: presented word problem re
-- statement:
--   Uniform recursive enumerability of trivial words in finite presentations.
--   Neither the presentation nor the word is fixed in this predicate.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L203-L208
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L203-L208

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.presented_word_problem_re {α : Type*} [Primcodable α] [DecidableEq α] :
    REPred (fun input : List (FreeGroup α) × FreeGroup α =>
      PresentedGroup.mk {r | r ∈ input.1} input.2 = 1) := by sorry
