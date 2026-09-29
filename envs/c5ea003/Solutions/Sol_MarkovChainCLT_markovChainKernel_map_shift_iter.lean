-- Prove2me | solution 1 for MarkovChainCLT.markovChainKernel_map_shift_iter
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:29:53.447007+00:00
-- url     : https://prove2.me/submissions/5f3511d4-cde1-42df-a912-9da2ebef7162

import Definitions.Def_MarkovErgodicity
import Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

/-- `Pᵏ` commutes with `P`. -/
lemma iter_comm {X : Type*} [MeasurableSpace X] (P : Kernel X X) (k : ℕ) :
    (iterKernel P k) ∘ₖ P = P ∘ₖ (iterKernel P k) := by
  induction k with
  | zero => rw [iterKernel_zero, Kernel.id_comp, Kernel.comp_id]
  | succ k ih => rw [iterKernel_succ, Kernel.comp_assoc, ih]

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (k : ℕ) :
    (BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => fun n => ω (n + k))
      = (BanditAlgorithm.markovChainKernel P) ∘ₖ (iterKernel P k) := by
  have hsh : ∀ j : ℕ, Measurable (fun (ω : ℕ → X) => fun n => ω (n + j)) :=
    fun j => measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  induction k with
  | zero =>
    have h0 : (fun (ω : ℕ → X) => fun n => ω (n + 0)) = id := rfl
    rw [h0, Kernel.map_id, iterKernel_zero, Kernel.comp_id]
  | succ k ih =>
    have hfac : (fun (ω : ℕ → X) => fun n => ω (n + (k + 1)))
        = (fun (ω : ℕ → X) => fun n => ω (n + k)) ∘ (fun (ω : ℕ → X) => fun n => ω (n + 1)) :=
      rfl
    rw [hfac, Kernel.map_comp_right _ (hsh 1) (hsh k), markovChainKernel_map_shift,
      Kernel.map_comp, ih, Kernel.comp_assoc, iter_comm, iterKernel_succ]
