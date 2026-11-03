-- Prove2me | Theorems.Thm_levy_foundations_pointFamilySplitIndep
-- name    : levy_foundations_pointFamilySplitIndep
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:09:51.480437+00:00
-- url     : https://prove2.me/theorems/0c2bd8d9-49bd-47f4-bf2f-540d319065b3
-- title:
--   Independence of disjoint subfamilies of a Poisson point family
-- statement:
--   Any two injectively selected coordinate subfamilies with disjoint images in the combined Poisson count-and-mark index are independent as dependent product-valued random variables. This block independence is the engine for prefix-versus-next superposition counts.
-- source:
--   Adapted independently from Shmuel Link, LeanLevy/RandomMeasure/PoissonPointFamily.lean, IsPoissonPointFamily.indepFun_pointFamily_split (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory

theorem levy_foundations_pointFamilySplitIndep
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {S T : Type*} (φ : S → ℕ ⊕ ℕ × ℕ) (ψ : T → ℕ ⊕ ℕ × ℕ)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hST : ∀ s t, φ s ≠ ψ t) :
    IndepFun (fun ω (i : S) => LevyFoundations.pointFamilyCombined K X (φ i) ω)
      (fun ω (j : T) => LevyFoundations.pointFamilyCombined K X (ψ j) ω) μ := by sorry
