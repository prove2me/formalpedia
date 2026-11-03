-- Prove2me | Theorems.Thm_levy_foundations_prmEvalSigmaLe
-- name    : levy_foundations_prmEvalSigmaLe
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:38:33.849725+00:00
-- url     : https://prove2.me/theorems/9a53c7a3-0b25-4cdc-b6fa-a7ec453c6b6d
-- title:
--   Poisson evaluation sigma-algebra is a sub-sigma-algebra
-- statement:
--   Given measurable counts and marks, every generated Poisson-evaluation event is measurable in the underlying sample-space σ-algebra.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently formulated Prove2Me draft; remote elaboration and proof pending. PoissonFiltration.lean lines 82–87.

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalSigma
import Theorems.Thm_levy_foundations_measurablePRMEval

open MeasureTheory

theorem levy_foundations_prmEvalSigmaLe
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) (R : Set E)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) :
    LevyFoundations.prmEvalSigma K X m R ≤
      (inferInstance : MeasurableSpace Ω) := by sorry
