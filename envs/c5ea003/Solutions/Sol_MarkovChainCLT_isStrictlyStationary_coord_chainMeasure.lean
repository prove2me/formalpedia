-- Prove2me | solution 1 for MarkovChainCLT.isStrictlyStationary_coord_chainMeasure
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T16:29:45.473467+00:00
-- url     : https://prove2.me/submissions/86e41553-7094-4a6f-8ad5-9bc4571908e2

import Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MixingCoefficients

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) := by
  have hm1 : Measurable (fun ω : ℕ → X => fun n => ω (n + 1)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1))
  have hmk : ∀ j : ℕ, Measurable (fun (ω : ℕ → X) => fun n => ω (n + j)) :=
    fun j => measurable_pi_lambda _ (fun n => measurable_pi_apply (n + j))
  have hshift1 : Measure.map (fun ω : ℕ → X => fun n => ω (n + 1)) (chainMeasure P π)
      = chainMeasure P π := by
    rw [chainMeasure, Measure.map_comp _ _ hm1, markovChainKernel_map_shift, ← Measure.comp_assoc, hinv]
  intro k
  have hid : Measure.map (fun (ω : ℕ → X) => fun n => ω n) (chainMeasure P π)
      = chainMeasure P π := by simp
  rw [hid]
  induction k with
  | zero => simp
  | succ j ih =>
    have hcomp : (fun (ω : ℕ → X) => fun n => ω (n + (j + 1)))
        = (fun ω : ℕ → X => fun n => ω (n + 1)) ∘ (fun (ω : ℕ → X) => fun n => ω (n + j)) := by
      funext ω n; simp [Nat.add_comm, Nat.add_left_comm]
    rw [hcomp, ← Measure.map_map hm1 (hmk j), ih, hshift1]
