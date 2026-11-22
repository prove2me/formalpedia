-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_stages_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.stages_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:11.758295+00:00
-- url     : https://prove2.me/theorems/3b410286-fd81-4163-8b1f-d25a02142832
-- title:
--   Computable Closure: stages primrec
-- statement:
--   The Computable Closure construction uses the stages primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L146-L150
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L146-L150

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit [DecidableEq G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.stages_primrec : Primrec (fun p : (List G × List G) × ℕ => stages p.1.1 p.1.2 p.2) := by sorry
