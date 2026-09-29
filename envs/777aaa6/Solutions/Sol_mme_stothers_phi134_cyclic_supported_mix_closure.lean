-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_supported_mix_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:55:19.565065+00:00
-- url     : https://prove2.me/submissions/6686f484-eb18-4f3a-810f-0a6858cfdcc0

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_marginals_force_exact_profile

open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupport : CyclicCoordinatewiseSupported x y z) :
    ∃ e : CyclicExactEdge N alpha beta gamma delta,
      cyclicModeWord e 0 = cyclicModeWord x 0 ∧
      cyclicModeWord e 1 = cyclicModeWord y 1 ∧
      cyclicModeWord e 2 = cyclicModeWord z 2 := by
  let e₀m := mixedMarginalAddress x.1.1 y.1.1 z.1.1 hsupport.1
  let e₁m := mixedMarginalAddress
    y.2.1.1 z.2.1.1 x.2.1.1 hsupport.2.1
  let e₂m := mixedMarginalAddress
    z.2.2.1 x.2.2.1 y.2.2.1 hsupport.2.2
  let e₀ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₀m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₀m⟩
  let e₁ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₁m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₁m⟩
  let e₂ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₂m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₂m⟩
  exact ⟨(e₀, (e₁, e₂)), rfl, rfl, rfl⟩
