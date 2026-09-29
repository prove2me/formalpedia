-- Prove2me | Theorems.Thm_IITTensorNetwork_entanglementEntropy_le_log_schmidtRank
-- name    : IITTensorNetwork.entanglementEntropy_le_log_schmidtRank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:02:11.581855+00:00
-- url     : https://prove2.me/theorems/f16f2785-f3df-47b1-84de-ad4d32891248
-- title:
--   Entropy–Schmidt rank bound.
-- statement:
--   **Entropy–Schmidt rank bound.**  The entanglement entropy across a cut is at
--   most the logarithm of the Schmidt rank.
--
--   ```lean
--   theorem IITTensorNetwork.entanglementEntropy_le_log_schmidtRank{M : Matrix α β ℂ} (hM : Normalized M) :
--       entanglementEntropy M ≤ Real.log (schmidtRank M) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkSchmidt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkSchmidt.lean#L113

-- Thm stub generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

/-! # Bipartite pure states, Schmidt rank and quantum mutual information

A pure state of a bipartite quantum system `A ⊗ B` with finite local index sets
`α` and `β` is encoded by its coefficient matrix `M : Matrix α β ℂ`, normalized
by `∑ i j, ‖M i j‖ ^ 2 = 1`.  The two reduced density matrices are `M * Mᴴ`
(on `A`) and `Mᴴ * M` (on `B`), the *Schmidt rank* across the cut is the rank of
`M`, and, since the global state is pure, the quantum mutual information across
the cut is

`I(A : B) = S(ρ_A) + S(ρ_B) - S(ρ_AB) = S(ρ_A) + S(ρ_B)`.

Main results:

* `rhoLeft_trace`, `rhoRight_trace` : the reduced matrices are density matrices;
* `schmidtRank_pos` : the Schmidt rank of a normalized state is at least one;
* `mutualInformation_nonneg`;
* `mutualInformation_le_two_log_schmidtRank` : the mutual information across a
  cut is at most `2 log (Schmidt rank)`;
* `mutualInformation_eq_zero_iff_schmidtRank_eq_one` : the mutual information
  vanishes exactly for product states across the cut;
* `vnEntropy_rhoLeft_eq_rhoRight` : the two marginal entropies of a pure state
  agree (equal-dimension parts), so `I(A : B) = 2 S(ρ_A)`;
* `mutualInformation_flat` : a flat Schmidt spectrum of rank `r` gives
  `I(A : B) = 2 log r`, the maximum allowed by the Schmidt rank.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
















omit [DecidableEq β] in

theorem IITTensorNetwork.entanglementEntropy_le_log_schmidtRank{M : Matrix α β ℂ} (hM : Normalized M) :
    entanglementEntropy M ≤ Real.log (schmidtRank M) := by sorry
