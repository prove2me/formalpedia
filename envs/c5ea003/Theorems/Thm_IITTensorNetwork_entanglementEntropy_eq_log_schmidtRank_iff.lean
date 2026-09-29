-- Prove2me | Theorems.Thm_IITTensorNetwork_entanglementEntropy_eq_log_schmidtRank_iff
-- name    : IITTensorNetwork.entanglementEntropy_eq_log_schmidtRank_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:05:12.447435+00:00
-- url     : https://prove2.me/theorems/b7df0879-6f59-40f5-882b-2699740573f5
-- title:
--   Equality in the entropy–Schmidt-rank bound.
-- statement:
--   **Equality in the entropy–Schmidt-rank bound.**  The entanglement entropy
--   across a cut equals `log (Schmidt rank)` exactly at a flat Schmidt spectrum.
--
--   ```lean
--   theorem IITTensorNetwork.entanglementEntropy_eq_log_schmidtRank_iff{M : Matrix α β ℂ} (hM : Normalized M) :
--       entanglementEntropy M = Real.log (schmidtRank M) ↔ FlatSchmidtSpectrum M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEquality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEquality.lean#L261

-- Thm stub generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

/-! # Equality analysis for the entropy bounds of integrated information

The companion files prove the inequalities

* `sum_negMulLog_le_log_card_support` : `H(p) ≤ log |supp p|`;
* `vnEntropy_le_log_rank`             : `S(ρ) ≤ log (rank ρ)`;
* `mutualInformation_le_two_log_schmidtRank` : `I(A:B) ≤ 2 log (Schmidt rank)`;
* `phi_le_two_log_of_bondDim`         : `Φ ≤ 2 log χ`.

Here we settle the *equality cases*: each of these bounds is saturated exactly
when the relevant spectrum is **flat**, i.e. uniform on its support.  This is
the missing "only if" half of the saturation analysis, and it is what makes the
value `Φ(GHZ) = 2 log d` an extremal, not merely an example, computation.

Main results:

* `sum_negMulLog_eq_log_card_support_iff` : `H(p) = log |supp p|` iff `p` is
  uniform on its support;
* `vnEntropy_eq_log_rank_iff` : a density matrix saturates the maximal entropy
  bound iff its nonzero eigenvalues all equal `1 / rank`;
* `entanglementEntropy_eq_log_schmidtRank_iff` and
  `mutualInformation_eq_two_log_schmidtRank_iff` : the Schmidt-rank bound on the
  mutual information across a cut is saturated exactly at a flat Schmidt
  spectrum;
* `phi_lt_two_log_of_nonflat_cut` : if some cut of a chain state has a
  non-flat marginal spectrum, then `Φ` is *strictly* below the bound
  `2 log (Schmidt rank)` at that cut.

We also formalize the "product cut" mechanism behind reducibility:
`schmidtRank_eq_one_of_product` and `phi_eq_zero_of_product_cut` show that a
chain state which factorizes across one bipartition has `Φ = 0`, so integrated
information is destroyed by a single product cut no matter how entangled the
two blocks are internally.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork

/-! ## Equality in the maximal entropy bound -/


variable {ι : Type*} [Fintype ι]







/-! ## Equality in the von Neumann bound -/


variable {m : Type*} [Fintype m] [DecidableEq m]





/-! ## Equality in the Schmidt-rank bound for mutual information -/


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]





omit [DecidableEq β] in

theorem IITTensorNetwork.entanglementEntropy_eq_log_schmidtRank_iff{M : Matrix α β ℂ} (hM : Normalized M) :
    entanglementEntropy M = Real.log (schmidtRank M) ↔ FlatSchmidtSpectrum M := by sorry
