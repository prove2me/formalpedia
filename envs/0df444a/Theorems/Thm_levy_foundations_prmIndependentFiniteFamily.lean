-- Prove2me | Theorems.Thm_levy_foundations_prmIndependentFiniteFamily
-- name    : levy_foundations_prmIndependentFiniteFamily
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:05:36.65799+00:00
-- url     : https://prove2.me/theorems/34f8a811-0862-452e-86a5-61d6e5be506b
-- title:
--   Mutual independence of finite families of disjoint-region Poisson counts
-- statement:
--   For any finite family of pairwise-disjoint measurable finite-intensity sets, their Poisson counts are mutually independent. This supplies a finite-dimensional independence bridge towards sigma-algebra independence.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonFiltration.lean. New Prove2Me proof target pending exact-revision elaboration. Based on the source finite-family independence arguments and the independent point-family counting law.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmIndependentFiniteFamily
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {n : ℕ} (A : Fin n → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => LevyFoundations.poissonRandomMeasure K X ω (A i)) μ := by sorry
