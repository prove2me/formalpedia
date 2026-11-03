-- Prove2me | Theorems.Thm_levy_foundations_prmIndependentCountFamilies
-- name    : levy_foundations_prmIndependentCountFamilies
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T18:05:49.636505+00:00
-- url     : https://prove2.me/theorems/29eb4fc9-30c0-474f-bf04-0f6d54834bb5
-- title:
--   Mutual independence of finite Poisson count-vector families on disjoint regions
-- statement:
--   Within each group, evaluation sets may overlap, but different groups are setwise disjoint. The finite-dimensional vectors of Poisson count evaluations are mutually independent across groups, allowing independence to pass to generated σ-algebras.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending remote Lean verification. RandomMeasure/PoissonFiltration.lean, iIndepFun_poissonRandomMeasure_families; uses partition into finitely many measurable atoms.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmIndependentCountFamilies
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {ιB : ι → Type*} [∀ i, Fintype (ιB i)]
    (B : ∀ i, ιB i → Set E)
    (hB : ∀ i b, MeasurableSet (B i b))
    (hfin : ∀ i b, m (B i b) < ⊤)
    (hdisj : ∀ i j, i ≠ j → ∀ b b',
      Disjoint (B i b) (B j b')) :
    iIndepFun
      (fun i ω (b : ιB i) =>
        LevyFoundations.poissonRandomMeasure K X ω (B i b)) μ := by sorry
