-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_ambient_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:37:44.199188+00:00
-- url     : https://prove2.me/submissions/03ffd7de-80a6-4496-9e86-1882c88c531b

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N alpha beta gamma delta : ℕ}
    (x y z : MME.StothersFourth.Phi233.CyclicAmbientEdge
      N alpha beta gamma delta)
    (hsupport :
      MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z) :
    ∃ e : MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta,
      MME.StothersFourth.Phi233.cyclicModeWord e 0 =
          MME.StothersFourth.Phi233.cyclicModeWord x 0 ∧
      MME.StothersFourth.Phi233.cyclicModeWord e 1 =
          MME.StothersFourth.Phi233.cyclicModeWord y 1 ∧
      MME.StothersFourth.Phi233.cyclicModeWord e 2 =
          MME.StothersFourth.Phi233.cyclicModeWord z 2 := by
  let e₀ := MME.StothersFourth.Phi233.mixedMarginalAddress
    x.1 y.1 z.1 hsupport.1
  let e₁ := MME.StothersFourth.Phi233.mixedMarginalAddress
    y.2.1 z.2.1 x.2.1 hsupport.2.1
  let e₂ := MME.StothersFourth.Phi233.mixedMarginalAddress
    z.2.2 x.2.2 y.2.2 hsupport.2.2
  exact ⟨(e₀, (e₁, e₂)), rfl, rfl, rfl⟩
