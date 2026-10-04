-- Prove2me | solution 1 for IITTensorNetwork.phi_le_mutualInformation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T13:55:07.988206+00:00
-- url     : https://prove2.me/submissions/3e308471-3ab1-40ba-8205-3ade2d68a171

import Theorems.Thm_IntegratedInformation_phi_le_loss
-- Thm stub generated from Novelty/IITTensorNetworkPhi.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IntegratedInformation

/-! # Integrated information of a tensor network state

We attach to a quantum state of a chain of `n` sites with local dimension `d`
the integrated information `Φ` of Tononi's theory, formalized through the
catalog's `IntegratedInformation.CausalStructure`: the admissible cuts are the
`n - 1` bipartitions of the chain into a left block and a right block, and the
information destroyed by a cut is the quantum mutual information carried across
that cut by the state.  Thus, *by construction*,

`Φ = min over bipartitions of the quantum mutual information`,

and the substantive content is in the theorems relating `Φ` to the tensor
network data:

* `phi_le_mutualInformation`, `exists_minimal_cut` : `Φ` is the minimum of the
  mutual information over bipartitions;
* `phi_eq_zero_iff_exists_product_cut` : `Φ = 0` exactly when the state
  factorizes (Schmidt rank one) across some cut, i.e. exactly when the state is
  *reducible* in the sense of IIT;
* `phi_le_two_log_of_bondDim` : a cut of bond dimension `χ` caps `Φ` at
  `2 log χ` — an MPS with bond dimension `2` has `Φ ≤ 2 log 2 = log 4`;
* `phi_ghz`, `phi_ghz_saturates_bond_bound` : the GHZ chain state has
  `Φ = 2 log d` where `d` is both its bond dimension
  (`hasBondDim_chainCutMatrix_ghz`) and its Schmidt rank at every cut; for
  `d = 2` this gives `Φ = 2 log 2 = log 4`, twice the logarithm of the Schmidt
  rank `2` (`phi_ghz_qubits`).
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork


variable {n d : ℕ}












variable {psi : (Fin n → Fin d) → ℂ}

theorem solution (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n)
    (p : Fin (n - 1)) :
    Phi hpsi hn
      ≤ mutualInformation (chainCutMatrix psi ((p : ℕ) + 1) (by have := p.isLt; omega)) := by
  simpa [IITTensorNetwork.Phi, IITTensorNetwork.chainCausalStructure] using
    IntegratedInformation.phi_le_loss (IITTensorNetwork.chainCausalStructure hpsi hn) p
