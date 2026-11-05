-- Prove2me | Theorems.Thm_levy_foundations_projectiveFamily_nonempty
-- name    : levy_foundations_projectiveFamily_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:11:53.41668+00:00
-- url     : https://prove2.me/theorems/060e8fdd-387d-40f7-8700-029b8853bd98
-- title:
--   A projective family forces every coordinate space to be inhabited
-- statement:
--   If every finite-coordinate marginal is a probability measure and the marginal family is projectively consistent, each individual coordinate space is nonempty. No nonemptiness assumption is made on the index type.
-- source:
--   Shmuel Link, LeanLevy, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Processes/Kolmogorov.lean: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean (`nonempty_of_projective`).

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem levy_foundations_projectiveFamily_nonempty
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α) (i : ι) :
    Nonempty (α i) := by sorry
