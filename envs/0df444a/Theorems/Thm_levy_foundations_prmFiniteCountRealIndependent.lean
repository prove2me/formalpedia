-- Prove2me | Theorems.Thm_levy_foundations_prmFiniteCountRealIndependent
-- name    : levy_foundations_prmFiniteCountRealIndependent
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T18:05:16.741088+00:00
-- url     : https://prove2.me/theorems/22c38494-f678-4420-895b-d226a507470d
-- title:
--   Finite disjoint Poisson counts are mutually independent after conversion to real values
-- statement:
--   The real-valued count vector on finitely many disjoint finite-intensity sets has mutually independent coordinates. Proof follows factorisation of its joint characteristic function, then applies the pinned Mathlib independence characterisation.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending remote Lean verification. RandomMeasure/PoissonRandomMeasure.lean, iIndepFun_natCast_poissonRandomMeasure_apply, and its characteristic-function proof.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmFiniteCountRealIndependent
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {n : ℕ} (A : Fin n → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun
      (fun i ω => (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal)
      μ := by sorry
