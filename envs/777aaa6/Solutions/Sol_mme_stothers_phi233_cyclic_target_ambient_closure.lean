-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_target_ambient_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:48:05.966732+00:00
-- url     : https://prove2.me/submissions/5a02e5d9-7212-4568-b730-aa9966b68071

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets

open MME

set_option autoImplicit false
set_option warningAsError true

/-- The concrete cyclic target/ambient finsets satisfy exactly the static
closure interface required by the generic type-2 hash-isolation theorem. -/
theorem solution
    (N alpha beta gamma delta : ℕ) :
    MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta ⊆
      MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta ∧
    ∀ x ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
      ∀ y ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ∀ z ∈ MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta,
          MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ MME.StothersFourth.Phi233.ambientFinset
                N alpha beta gamma delta,
              MME.StothersFourth.Phi233.cyclicModeWord e 0 =
                  MME.StothersFourth.Phi233.cyclicModeWord x 0 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 1 =
                  MME.StothersFourth.Phi233.cyclicModeWord y 1 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 2 =
                  MME.StothersFourth.Phi233.cyclicModeWord z 2 := by
  constructor
  · intro x hx
    classical
    simp [MME.StothersFourth.Phi233.ambientFinset]
  · intro x hx y hy z hz hsupport
    let e₀ := MME.StothersFourth.Phi233.mixedMarginalAddress
      x.1 y.1 z.1 hsupport.1
    let e₁ := MME.StothersFourth.Phi233.mixedMarginalAddress
      y.2.1 z.2.1 x.2.1 hsupport.2.1
    let e₂ := MME.StothersFourth.Phi233.mixedMarginalAddress
      z.2.2 x.2.2 y.2.2 hsupport.2.2
    refine ⟨(e₀, (e₁, e₂)), ?_, rfl, rfl, rfl⟩
    classical
    simp [MME.StothersFourth.Phi233.ambientFinset]
