-- Prove2me | solution 1 for MarkovChainCLT.isStrictlyStationary_chainMeasure
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:21:06.006997+00:00
-- url     : https://prove2.me/submissions/cfcc9de9-7d59-4a05-b711-1be5fa0d9670

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_chainMeasure_map_shift

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) := by
  have hσ : Measurable (fun (ω : ℕ → X) => fun n => ω (n + 1)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hsh : ∀ k : ℕ, Measurable (fun (ω : ℕ → X) => fun n => ω (n + k)) :=
    fun k => measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hfac : (fun (ω : ℕ → X) => fun n => ω (n + (k + 1)))
        = (fun (ω : ℕ → X) => fun n => ω (n + k)) ∘ (fun (ω : ℕ → X) => fun n => ω (n + 1)) :=
      rfl
    rw [hfac, ← Measure.map_map (hsh k) hσ, chainMeasure_map_shift P π hinv, ih]
