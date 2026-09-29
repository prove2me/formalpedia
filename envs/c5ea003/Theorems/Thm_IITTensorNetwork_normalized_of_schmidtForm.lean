-- Prove2me | Theorems.Thm_IITTensorNetwork_normalized_of_schmidtForm
-- name    : IITTensorNetwork.normalized_of_schmidtForm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:07:00.464229+00:00
-- url     : https://prove2.me/theorems/fa435e24-18ab-4c37-82f6-6a3cbac021a3
-- title:
--   A state in Schmidt form is normalized exactly when its Schmidt coefficients
-- statement:
--   A state in Schmidt form is normalized exactly when its Schmidt coefficients
--   form a unit vector.
--
--   ```lean
--   theorem IITTensorNetwork.normalized_of_schmidtForm{M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
--       {w : γ → ℝ} (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1)
--       (hM : M = L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ) (hw : ∑ k, w k ^ 2 = 1) :
--       Normalized M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkWeightedGHZ.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkWeightedGHZ.lean#L129

-- Thm stub generated from Novelty/IITTensorNetworkWeightedGHZ.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
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





omit [DecidableEq α] [DecidableEq β] in

theorem IITTensorNetwork.normalized_of_schmidtForm{M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    {w : γ → ℝ} (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1)
    (hM : M = L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ) (hw : ∑ k, w k ^ 2 = 1) :
    Normalized M := by sorry
