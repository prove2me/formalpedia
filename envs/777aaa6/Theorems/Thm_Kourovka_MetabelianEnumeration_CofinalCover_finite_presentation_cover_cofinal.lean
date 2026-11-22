-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_finite_presentation_cover_cofinal
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_cover_cofinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:24:25.116067+00:00
-- url     : https://prove2.me/theorems/4907319c-1543-42c5-bed3-efbb36d14efd
-- title:
--   Cofinal Cover: finite presentation cover cofinal
-- statement:
--   Cofinality of the concrete finite-cover family. The lattice rank is the
--   original number of generators and the kernel alphabet is nonempty. Neither
--   tameness nor any presentation theorem is assumed in the conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/Cofinality.lean#L27-L54
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/Cofinality.lean#L27-L54

import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Definitions.Def_Kourovka_Cofinality_Cofinality
set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ValuationModule SignedTameness
open TamenessCompactness

theorem Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_cover_cofinal {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →*
        PresentedGroup (CentralExtension.relSet R), Function.Surjective f := by sorry
