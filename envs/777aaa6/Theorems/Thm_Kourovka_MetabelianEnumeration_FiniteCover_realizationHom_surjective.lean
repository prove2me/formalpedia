-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_realizationHom_surjective
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:22.024975+00:00
-- url     : https://prove2.me/theorems/a4d69af8-981d-4d20-8b0e-d1373a32834a
-- title:
--   Finite Cover: realization Hom surjective
-- statement:
--   The induced homomorphism is surjective when the chosen images generate the target.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L203-L216
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L203-L216

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Definitions.Def_Kourovka_Covers_FiniteCover
set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover

theorem Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_surjective {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A)
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    Function.Surjective (realizationHom data radius t A h) := by sorry
