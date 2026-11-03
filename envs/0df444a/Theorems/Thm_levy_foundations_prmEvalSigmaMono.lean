-- Prove2me | Theorems.Thm_levy_foundations_prmEvalSigmaMono
-- name    : levy_foundations_prmEvalSigmaMono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:19:33.478985+00:00
-- url     : https://prove2.me/theorems/75052dcc-bf41-493a-bf72-a4306a33db9f
-- title:
--   Monotonicity of Poisson evaluation sigma-algebras
-- statement:
--   If R is contained in S, observations of Poisson random-measure evaluations inside R generate a sub-σ-algebra of those inside S.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently formulated Prove2Me draft; remote elaboration and proof pending. PoissonFiltration.lean lines 75–79.

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalSigma

open MeasureTheory

theorem levy_foundations_prmEvalSigmaMono
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) {R S : Set E} (hRS : R ⊆ S) :
    LevyFoundations.prmEvalSigma K X m R ≤
      LevyFoundations.prmEvalSigma K X m S := by sorry
