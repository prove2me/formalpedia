-- Prove2me | solution 1 for Bridges.AlgebraMachineLearning.quotient_neural_universal_factor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:55:40.218221+00:00
-- url     : https://prove2.me/submissions/04113e4a-9714-4d66-a415-f5fb30334765

import Mathlib
import Definitions.Def_Bridges_PosetTheory_CoalgebraicNeuralMyhillNerode

open Classical Bridges.AlgebraMachineLearning in
theorem solution {σ τ α β : Type*}
    {N : NeuralObservationSystem σ α β}
    {M : NeuralObservationSystem τ α β}
    (f : NeuralHom N M)
    (hf : ∀ s t, neural_equiv N s t → f.toFun s = f.toFun t) :
    ∃ g : Quotient (neural_setoid N) → τ,
      (∀ s : σ, g (Quotient.mk _ s) = f.toFun s) ∧
      (∀ q a, g ((quotient_neural_system N).step q a) = M.step (g q) a) ∧
      (∀ q, (quotient_neural_system N).observe q = M.observe (g q)) := by
  -- `f` descends to the behavioural quotient
  refine ⟨Quotient.lift f.toFun (fun s t h => hf s t h), fun s => rfl, ?_, ?_⟩
  · intro q a
    induction q using Quotient.inductionOn with
    | h s => exact f.map_step s a
  · intro q
    induction q using Quotient.inductionOn with
    | h s => exact f.map_observe s
