-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_symbols_cover
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.symbols_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:19:43.431+00:00
-- url     : https://prove2.me/theorems/469afdfd-7049-4b48-b62b-7229ef9ab540
-- title:
--   Schreier Heights: symbols cover
-- statement:
--   The Schreier Heights construction uses the symbols cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceRelators.lean#L39-L56
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceRelators.lean#L39-L56

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.symbols_cover (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (D μ : ℝ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : D ≤ μ)
    (z : S.Edge) :
    z ∈ symbolsIn (χ.comp π) S (fun x => 0 ≤ x) ∨
      z ∈ symbolsIn (χ.comp π) S (fun x => x ≤ μ) := by sorry
