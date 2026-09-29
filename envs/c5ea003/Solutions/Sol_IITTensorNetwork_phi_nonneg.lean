-- Prove2me | solution 1 for IITTensorNetwork.phi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:29:05.050347+00:00
-- url     : https://prove2.me/submissions/879db880-6cd1-4ee2-8391-011d791605c6

import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IntegratedInformation

open Finset Matrix
open scoped ComplexOrder
open IITTensorNetwork

variable {n d : ℕ}
variable {psi : (Fin n → Fin d) → ℂ}

theorem solution (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) : 0 ≤ Phi hpsi hn := by
  dsimp [Phi, IntegratedInformation.Phi]
  apply Finset.le_min'
  intro y hy
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hy
  exact (chainCausalStructure hpsi hn).loss_nonneg c
