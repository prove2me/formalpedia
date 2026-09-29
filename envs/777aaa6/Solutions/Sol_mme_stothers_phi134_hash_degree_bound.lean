-- Prove2me | solution 1 for mme_stothers_phi134_hash_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:19:22.156309+00:00
-- url     : https://prove2.me/submissions/38a7fc31-929b-4575-a80e-81add722a18e

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_cyclic_mode_fiber_card

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

noncomputable section

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    [DecidableEq (CyclicModeWord N)] :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    ∀ i : Fin 3,
      ∀ e ∈ edgeFinset N alpha beta gamma delta,
        ((edgeFinset N alpha beta gamma delta).filter
          (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤
            D 0 * (D 1 * D 2) := by
  classical
  dsimp only
  intro i e _he
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  have h := mme_stothers_phi134_cyclic_mode_fiber_card
    N alpha beta gamma delta hsum e i
  rw [Nat.card_eq_fintype_card] at h
  change ((Finset.univ : Finset
      (CyclicExactEdge N alpha beta gamma delta)).filter
        (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤ _
  rw [← Fintype.card_subtype]
  exact h.le
