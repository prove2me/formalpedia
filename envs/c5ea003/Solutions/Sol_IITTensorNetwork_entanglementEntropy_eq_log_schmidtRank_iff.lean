-- Prove2me | solution 1 for IITTensorNetwork.entanglementEntropy_eq_log_schmidtRank_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:46:01.486359+00:00
-- url     : https://prove2.me/submissions/99e2d6d2-a685-4a90-abec-196bec0328d4

-- Sol generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_rank_eq_card_support
import Theorems.Thm_IITTensorNetwork_rank_rhoLeft
import Theorems.Thm_IITTensorNetwork_sum_eigenvalues_eq_one
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_eq_log_card_support_iff
import Theorems.Thm_IITTensorNetwork_vnEntropy_of_isHermitian

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

/-- **Equality in the maximal entropy bound for density matrices.**  A density
matrix saturates `S(ρ) ≤ log (rank ρ)` exactly when its nonzero eigenvalues are
all equal to `1 / rank ρ`, i.e. exactly when its spectrum is flat. -/
theorem vnEntropy_eq_log_rank_iff {A : Matrix m m ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    vnEntropy A = Real.log A.rank ↔
      ∀ i ∈ support hA.isHermitian.eigenvalues,
        hA.isHermitian.eigenvalues i = ((A.rank : ℝ))⁻¹ := by
  have hrk : A.rank = (support hA.isHermitian.eigenvalues).card :=
    rank_eq_card_support hA.isHermitian
  rw [vnEntropy_of_isHermitian hA.isHermitian, hrk]
  exact sum_negMulLog_eq_log_card_support_iff hA.eigenvalues_nonneg
    (sum_eigenvalues_eq_one hA htr)




/-! ## Equality in the Schmidt-rank bound for mutual information -/


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]











/-! ## Product cuts destroy integrated information -/


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]






/-! ## Consequences for the integrated information of a chain -/


variable {n d : ℕ} {psi : (Fin n → Fin d) → ℂ}







/-! ## Concatenation of two chains -/


variable {n d : ℕ}







open IITTensorNetwork in
omit [DecidableEq β] in
theorem solution{M : Matrix α β ℂ} (hM : Normalized M) :
    entanglementEntropy M = Real.log (schmidtRank M) ↔ FlatSchmidtSpectrum M := by
  have h := vnEntropy_eq_log_rank_iff (rhoLeft_posSemidef M) (rhoLeft_trace hM)
  rw [rank_rhoLeft] at h
  exact h
