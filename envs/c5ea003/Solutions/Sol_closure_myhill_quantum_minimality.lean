-- Prove2me | solution 1 for closure_myhill_quantum_minimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:07:57.257642+00:00
-- url     : https://prove2.me/submissions/012486b6-9b47-4ab6-b15e-f9a09425bd7b

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_AlgebraEMLClosureComputation
theorem solution {σ : Type*} {α : Type*} {K : Type*} [Semiring K]
    (M : ClosureSemimoduleSystem σ α K) (P : ProbeFamily σ K)
    (R : ObservableRealization α K) (hRed : R.isReduced)
    (φ : TracePreservingMap M P R) :
    ∃ f : Quotient (ClosureSetoid M P) → R.σR, Function.Injective f := by
  -- indistinguishable states land on trace-equal, hence equal, realized states
  refine ⟨Quotient.lift φ.map (fun s t hst => hRed _ _ (fun w => by
    rw [← φ.preserves, ← φ.preserves]
    exact hst w)), ?_⟩
  -- and equal images force equal traces back in the original system
  intro a b hab
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply Quotient.sound
  intro w
  have h := congrArg (fun r => ClosureTrace R.sys R.probes r w) hab
  simp only [Quotient.lift_mk] at h
  rw [φ.preserves, φ.preserves]
  exact h
