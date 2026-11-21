-- Prove2me | Theorems.Thm_Kourovka_abelianization_map_surjective
-- name    : Kourovka.abelianization_map_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:23.185697+00:00
-- url     : https://prove2.me/theorems/4860d11f-1b8b-4116-8a74-f7e77b9d820f
-- title:
--   Kourovka: abelianization map surjective
-- statement:
--   The Kourovka construction uses the abelianization map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Hopfian.lean#L43-L48
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Hopfian.lean#L43-L48

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
import Definitions.Def_Kourovka_Hopfian
set_option autoImplicit true
open Kourovka
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.abelianization_map_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by sorry
