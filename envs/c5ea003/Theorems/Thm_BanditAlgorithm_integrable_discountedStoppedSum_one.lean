-- Prove2me | Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one
-- name    : BanditAlgorithm.integrable_discountedStoppedSum_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:01:38.516359+00:00
-- url     : https://prove2.me/theorems/96c4a615-b114-48e7-b5ca-e9c84ed7a40e
-- title:
--   Integrability of stopped discounted time
-- statement:
--   For $0\leq\alpha<1$, the discounted amount of time accumulated before any adapted stopping time is integrable, because it is pathwise bounded by the convergent geometric series $\sum_{t\geq0}\alpha^t$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), denominator in Eq. (35.9), printed p.448.

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.integrable_discountedStoppedSum_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α (fun _ : S ↦ 1) τ)
      (markovChainMeasure P x) := by
  sorry
