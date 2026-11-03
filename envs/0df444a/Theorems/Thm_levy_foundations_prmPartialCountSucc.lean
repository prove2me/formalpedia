-- Prove2me | Theorems.Thm_levy_foundations_prmPartialCountSucc
-- name    : levy_foundations_prmPartialCountSucc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:22.561141+00:00
-- url     : https://prove2.me/theorems/76eab401-fb26-4bf2-ae3d-e7259b39be60
-- title:
--   Recurrence for the finite Poisson superposition count
-- statement:
--   Adding one further Poisson piece increases the finite superposition count by exactly the thinned count of that piece.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, finite sum recurrence used in charFunDual_prmPartialCountVec around line 830.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_prmPartialCount

open MeasureTheory

theorem levy_foundations_prmPartialCountSucc
    {Ω E : Type*} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (A : Set E)
    (n : ℕ) (ω : Ω) :
    LevyFoundations.prmPartialCount K X A (n + 1) ω =
      LevyFoundations.prmPartialCount K X A n ω +
        LevyFoundations.thinnedCount K X A (n + 1) ω := by sorry
