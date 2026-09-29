-- Prove2me | Theorems.Thm_IITTensorNetwork_sum_negMulLog_eq_log_card_support_iff
-- name    : IITTensorNetwork.sum_negMulLog_eq_log_card_support_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:05:17.685488+00:00
-- url     : https://prove2.me/theorems/9df8f117-14d6-42f2-b1b1-c42b7b38a72f
-- title:
--   Equality in the maximal entropy bound.
-- statement:
--   **Equality in the maximal entropy bound.**  The Shannon entropy of a
--   probability vector equals the logarithm of the size of its support exactly when
--   the vector is uniform on that support.
--
--   ```lean
--   theorem IITTensorNetwork.sum_negMulLog_eq_log_card_support_iff{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
--       (hsum : ∑ i, p i = 1) :
--       (∑ i, Real.negMulLog (p i)) = Real.log (support p).card ↔
--         ∀ i ∈ support p, p i = ((support p).card : ℝ)⁻¹ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEquality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEquality.lean#L103

-- Thm stub generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi

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

theorem IITTensorNetwork.sum_negMulLog_eq_log_card_support_iff{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) = Real.log (support p).card ↔
      ∀ i ∈ support p, p i = ((support p).card : ℝ)⁻¹ := by sorry
