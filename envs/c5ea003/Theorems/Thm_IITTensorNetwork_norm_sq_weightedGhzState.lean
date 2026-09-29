-- Prove2me | Theorems.Thm_IITTensorNetwork_norm_sq_weightedGhzState
-- name    : IITTensorNetwork.norm_sq_weightedGhzState
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:06:49.658997+00:00
-- url     : https://prove2.me/theorems/484ef2f5-f409-412f-9a3b-a5d34e3a53e3
-- title:
--   The squared modulus of the amplitude of a weighted GHZ state.
-- statement:
--   The squared modulus of the amplitude of a weighted GHZ state.
--
--   ```lean
--   theorem IITTensorNetwork.norm_sq_weightedGhzState(hn : 1 ≤ n) (s : Fin n → Fin d) :
--       ‖weightedGhzState n d w s‖ ^ 2 = ∑ x, if s = constCfg n d x then w x ^ 2 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkWeightedGHZ.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkWeightedGHZ.lean#L244

-- Thm stub generated from Novelty/IITTensorNetworkWeightedGHZ.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ

/-! # Schmidt form, weighted GHZ chains, and the exact value of `Φ`

This file completes the analysis of the mission conjecture "`Φ` is determined by
the Schmidt rank" by exhibiting, for every chain length `n ≥ 2` and every local
dimension `d`, a one-parameter family of matrix product states of *fixed* bond
dimension and *fixed* Schmidt rank `d` at every cut whose integrated information
sweeps out the whole interval `(0, 2 log d]`.

The tool is the *Schmidt form* of a bipartite pure state: a factorization

`M = L · diag(w) · Rᴴ`  with  `Lᴴ L = 1`,  `Rᴴ R = 1`,

i.e. an isometric change of basis on both sides bringing the state to diagonal
form with Schmidt coefficients `w`.  Main structural results:

* `vnEntropy_rhoLeft_of_schmidtForm`, `vnEntropy_rhoRight_of_schmidtForm`,
  `mutualInformation_of_schmidtForm` : the marginal entropies, and hence the
  mutual information across the cut, are the Shannon entropy of the squared
  Schmidt coefficients — *only the Schmidt spectrum matters*;
* `normalized_of_schmidtForm` : normalization is `∑ w² = 1`;
* `schmidtRank_of_schmidtForm` : the Schmidt rank is the number of Schmidt
  coefficients (when all are nonzero).

These are then applied to the **weighted GHZ chain state**
`ψ_w = ∑ₓ wₓ |x x ⋯ x⟩`, whose cut matrix is computed exactly
(`chainCutMatrix_weightedGhz`).  Consequences:

* `phi_weightedGhz` : `Φ(ψ_w) = 2 ∑ₓ -wₓ² log wₓ²` for every `n ≥ 2`;
* `schmidtRank_chainCutMatrix_weightedGhz` : the Schmidt rank at every cut is
  `d`, independently of `w`;
* `phi_unbalancedGhz_eq_two_mul_binEntropy` and
  `phi_unbalancedGhz_lt_two_log_two` : for `d = 2` the value is
  `2 H₂(c²)`, which is *strictly* below `2 log 2 = 2 log (Schmidt rank)`
  precisely when `c² ≠ 1/2`, while the state remains a bond-dimension-two MPS of
  Schmidt rank two at every bipartition.

Together with `phi_ghz` (the flat case) this settles the status of the
conjecture: `Φ` is bounded by, but not determined by, the Schmidt rank, and
equals `2 log (Schmidt rank)` exactly on flat spectra.
-/

open Finset Matrix Polynomial
open scoped ComplexOrder

open IITTensorNetwork

/-! ## States in Schmidt form -/


variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]










/-! ## The weighted GHZ chain state -/


variable {n d : ℕ} {w : Fin d → ℝ}

theorem IITTensorNetwork.norm_sq_weightedGhzState(hn : 1 ≤ n) (s : Fin n → Fin d) :
    ‖weightedGhzState n d w s‖ ^ 2 = ∑ x, if s = constCfg n d x then w x ^ 2 else 0 := by sorry
