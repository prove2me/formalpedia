-- Prove2me | Theorems.Thm_IITTensorNetwork_phi_pos_iff_all_cuts_entangled
-- name    : IITTensorNetwork.phi_pos_iff_all_cuts_entangled
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:06:32.900353+00:00
-- url     : https://prove2.me/theorems/4387145b-7c67-4d8e-9f59-088b75aa6744
-- title:
--   Irreducibility criterion.
-- statement:
--   **Irreducibility criterion.**  A chain state has strictly positive
--   integrated information exactly when it is entangled (Schmidt rank at least two)
--   across every bipartition.
--
--   ```lean
--   theorem IITTensorNetwork.phi_pos_iff_all_cuts_entangled(hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) :
--       0 < Phi hpsi hn ↔
--         ∀ p : Fin (n - 1),
--           2 ≤ schmidtRank (chainCutMatrix psi ((p : ℕ) + 1) (by have := p.isLt; omega)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkPhi.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkPhi.lean#L181

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

theorem IITTensorNetwork.phi_pos_iff_all_cuts_entangled(hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) :
    0 < Phi hpsi hn ↔
      ∀ p : Fin (n - 1),
        2 ≤ schmidtRank (chainCutMatrix psi ((p : ℕ) + 1) (by have := p.isLt; omega)) := by sorry
