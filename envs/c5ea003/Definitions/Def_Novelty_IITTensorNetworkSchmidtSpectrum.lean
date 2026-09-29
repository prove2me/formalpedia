-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
-- name    : Novelty_IITTensorNetworkSchmidtSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:53:15.220459+00:00
-- url     : https://prove2.me/theorems/142b6872-a5fc-433e-bc2c-98f08342e35a
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkSchmidtSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkSchmidtSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkSchmidtSpectrum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEquality

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

namespace IITTensorNetwork

/-! ## States in Schmidt-diagonal form -/

section DiagonalState

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The bipartite coefficient matrix determined by a real vector of Schmidt
coefficients: the diagonal matrix with those entries. -/
noncomputable def schmidtDiag (v : α → ℝ) : Matrix α α ℂ :=
  Matrix.diagonal (fun i => (v i : ℂ))









end DiagonalState

/-! ## Integrated information of a two-site chain -/

section TwoSites

variable {d : ℕ} {psi : (Fin 2 → Fin d) → ℂ}


end TwoSites

/-! ## The two-qubit family `c|00⟩ + s|11⟩` -/

section QubitPair

/-- The two-qubit state `c|00⟩ + s|11⟩`, a matrix product state of bond
dimension two whose Schmidt coefficients are `c` and `s`. -/
noncomputable def qubitPairState (c s : ℝ) : (Fin 2 → Fin 2) → ℂ :=
  fun t => if t 0 = t 1 then (if t 0 = 0 then (c : ℂ) else (s : ℂ)) else 0

/-- The Schmidt coefficient vector of the two-qubit family, indexed by the
configurations of a single site. -/
def qubitPairCoeff (c s : ℝ) : (Fin 1 → Fin 2) → ℝ :=
  fun f => if f 0 = 0 then c else s









end QubitPair

end IITTensorNetwork


