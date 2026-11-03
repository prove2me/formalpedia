-- Prove2me | Theorems.Thm_levy_foundations_projectiveFamilyMapMapRestrict
-- name    : levy_foundations_projectiveFamilyMapMapRestrict
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:18:00.015398+00:00
-- url     : https://prove2.me/theorems/474fe32a-57b5-4e38-81b2-98b5362080d0
-- title:
--   Composing projective marginal restrictions equals a single restriction
-- statement:
--   Composing projective marginal restrictions equals a single restriction.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/ProjectiveFamily.lean#L70

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem levy_foundations_projectiveFamilyMapMapRestrict
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    {I J K : Finset ι} (hJI : J ⊆ I) (hKJ : K ⊆ J) :
    ((pf.measure I).map (Finset.restrict₂ hJI)).map
      (Finset.restrict₂ hKJ) =
      (pf.measure I).map (Finset.restrict₂ (hKJ.trans hJI)) := by sorry
