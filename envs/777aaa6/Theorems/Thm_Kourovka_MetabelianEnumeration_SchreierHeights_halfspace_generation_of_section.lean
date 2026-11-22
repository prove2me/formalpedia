-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_halfspace_generation_of_section
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.halfspace_generation_of_section
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:08.193444+00:00
-- url     : https://prove2.me/theorems/09e87a8c-5518-419e-be6b-759827c3cbb5
-- title:
--   Schreier Heights: halfspace generation of section
-- statement:
--   The Schreier Heights construction uses the halfspace generation of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeneration.lean#L38-L100
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeneration.lean#L38-L100

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.halfspace_generation_of_section (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (χ : L →+ ℝ)
    (S : Transversal (preKernel R π))
    (D B μ : ℝ) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hμ : 2 * B ≤ μ)
    (hD : ∀ x, |value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R)))
      (FreeGroup.of x)| ≤ D)
    (hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B)
    (hsafe : ∀ t : S.vertices,
      PathIn (step (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))))
        (fun z => min 0 (value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) t.val) ≤ z ∧
          z ≤ max μ (value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) t.val))
        0 t.val.toWord)
    (habelian : ∀ a b : π.ker, Commute a b) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ μ)) = ⊤ := by sorry
