-- Prove2me | Theorems.Thm_IITTensorNetwork_phi_two_sites
-- name    : IITTensorNetwork.phi_two_sites
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:05:43.962696+00:00
-- url     : https://prove2.me/theorems/7e222ad3-585e-45d7-80eb-41adbdb4384d
-- title:
--   For a chain of two sites there is only one bipartition, so `Φ` is the mutual
-- statement:
--   For a chain of two sites there is only one bipartition, so `Φ` is the mutual
--   information across it.
--
--   ```lean
--   theorem IITTensorNetwork.phi_two_sites(hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) :
--       Phi hpsi (le_refl 2) = mutualInformation (chainCutMatrix psi 1 (by omega)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkSchmidtSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkSchmidtSpectrum.lean#L137

-- Thm stub generated from Novelty/IITTensorNetworkSchmidtSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum

/-! # Schmidt-diagonal states and the failure of "Φ = 2 log (Schmidt rank)"

The mission conjecture in its naive reading — that the integrated information of
a tensor network state is determined by its Schmidt rank — is *false*: the
mutual information across a cut depends on the whole Schmidt spectrum, not just
on the number of nonzero Schmidt coefficients.  The Schmidt rank only provides
the upper bound `2 log (Schmidt rank)` proved in the companion files, and the
bound is attained exactly at a flat spectrum (`IITTensorNetworkEquality`).

This file provides the explicit witness.  We work with states given in Schmidt
form: a real vector `v` of Schmidt coefficients yields the coefficient matrix
`schmidtDiag v = diagonal v`, for which everything is computable:

* `normalized_schmidtDiag_iff` : normalization is `∑ v i ^ 2 = 1`;
* `mutualInformation_schmidtDiag` : `I = 2 ∑ -v i² log (v i²)`;
* `schmidtRank_schmidtDiag` : the Schmidt rank is the number of nonzero
  coefficients;
* `mutualInformation_schmidtDiag_lt_of_not_flat` /
  `mutualInformation_schmidtDiag_of_flat` : the sharp dichotomy against the
  bound `2 log (card)`.

We then instantiate this with a one-parameter family of two-qubit states
`qubitPairState c s = c|00⟩ + s|11⟩` (a matrix product state of bond dimension
two) and prove:

* `phi_qubitPair` : `Φ = 2(-c² log c² - s² log s²)`;
* `schmidtRank_qubitPair` : the Schmidt rank is `2` whenever `c, s ≠ 0`;
* `phi_qubitPair_lt_two_log_two` : as soon as `c² ≠ 1/2` the integrated
  information is *strictly* below `2 log 2 = 2 log (Schmidt rank)`, so `Φ` is
  not a function of the Schmidt rank;
* `phi_bellPair` : at `c = s = 1/√2` the value `2 log 2` is attained, so the
  bound is sharp — the bond-dimension-two cap `Φ ≤ 2 log 2` of
  `mutualInformation_mps_bondDim_two_le` is exactly the Bell/GHZ value.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork

/-! ## States in Schmidt-diagonal form -/


variable {α : Type*} [Fintype α] [DecidableEq α]











/-! ## Integrated information of a two-site chain -/


variable {d : ℕ} {psi : (Fin 2 → Fin d) → ℂ}

theorem IITTensorNetwork.phi_two_sites(hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) :
    Phi hpsi (le_refl 2) = mutualInformation (chainCutMatrix psi 1 (by omega)) := by sorry
