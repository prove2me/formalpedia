-- Prove2me | solution 1 for IITTensorNetwork.mutualInformation_eq_two_mul_entanglementEntropy_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:42.82742+00:00
-- url     : https://prove2.me/submissions/1a3e97a6-41f8-43ee-8715-5432f212d782

-- Sol generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_vnEntropy_eq_multiset_sum

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

/-- Two Hermitian matrices whose characteristic polynomials differ by a power of
`X` (i.e. by extra zero eigenvalues) have the same von Neumann entropy. -/
lemma vnEntropy_eq_of_charpoly_eq_X_pow_mul {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : ℕ}
    (h : A.charpoly = Polynomial.X ^ k * B.charpoly) :
    vnEntropy A = vnEntropy B := by
  have hne : (Polynomial.X : Polynomial ℂ) ^ k * B.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic B).ne_zero
  rw [vnEntropy_eq_multiset_sum hA, vnEntropy_eq_multiset_sum hB, h,
    Polynomial.roots_mul hne, Polynomial.roots_pow, Polynomial.roots_X,
    Multiset.nsmul_singleton, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate]
  simp [Multiset.sum_replicate]

/-- **The two marginals of a bipartite pure state have the same entropy**, for
arbitrary (not necessarily equal) part dimensions: the two reduced density
matrices have the same nonzero spectrum. -/
theorem vnEntropy_rhoLeft_eq_rhoRight_general (M : Matrix α β ℂ) :
    vnEntropy (rhoLeft M) = vnEntropy (rhoRight M) := by
  rcases le_total (Fintype.card β) (Fintype.card α) with h | h
  · exact vnEntropy_eq_of_charpoly_eq_X_pow_mul (rhoLeft_posSemidef M).isHermitian
      (rhoRight_posSemidef M).isHermitian (Matrix.charpoly_mul_comm_of_le M Mᴴ h)
  · exact (vnEntropy_eq_of_charpoly_eq_X_pow_mul (rhoRight_posSemidef M).isHermitian
      (rhoLeft_posSemidef M).isHermitian (Matrix.charpoly_mul_comm_of_le Mᴴ M h)).symm









/-! ## Product cuts destroy integrated information -/


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]






/-! ## Consequences for the integrated information of a chain -/


variable {n d : ℕ} {psi : (Fin n → Fin d) → ℂ}







/-! ## Concatenation of two chains -/


variable {n d : ℕ}







open IITTensorNetwork in
theorem solution(M : Matrix α β ℂ) :
    mutualInformation M = 2 * entanglementEntropy M := by
  rw [mutualInformation, entanglementEntropy, ← vnEntropy_rhoLeft_eq_rhoRight_general M]
  ring
