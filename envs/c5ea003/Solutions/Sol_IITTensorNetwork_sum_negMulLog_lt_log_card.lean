-- Prove2me | solution 1 for IITTensorNetwork.sum_negMulLog_lt_log_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:46.629588+00:00
-- url     : https://prove2.me/submissions/873566fc-6e02-43b0-a85a-a17b4dd87517

-- Sol generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_eq_log_card_support_iff
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_le_log_card_support
import Theorems.Thm_IITTensorNetwork_support_nonempty

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











/-! ## Product cuts destroy integrated information -/


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]






/-! ## Consequences for the integrated information of a chain -/


variable {n d : ℕ} {psi : (Fin n → Fin d) → ℂ}







/-! ## Concatenation of two chains -/


variable {n d : ℕ}







open IITTensorNetwork in
theorem solution{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hne : ∃ i, p i ≠ ((Fintype.card ι : ℝ))⁻¹) :
    ∑ i, Real.negMulLog (p i) < Real.log (Fintype.card ι) := by
  classical
  set S := support p with hS
  have hSne : S.Nonempty := support_nonempty hsum
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hsub : S ⊆ Finset.univ := Finset.subset_univ _
  have hcardle : S.card ≤ Fintype.card ι := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  have hbound := sum_negMulLog_le_log_card_support hp hsum
  rw [← hS] at hbound
  rcases lt_or_eq_of_le hcardle with hlt | heqcard
  · have h1 : Real.log (S.card : ℝ) < Real.log (Fintype.card ι : ℝ) := by
      apply Real.log_lt_log
      · exact_mod_cast hcardpos
      · exact_mod_cast hlt
    linarith
  · -- the support is everything, so non-uniformity gives strictness
    have huniv : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [heqcard]
    obtain ⟨i0, hi0⟩ := hne
    have hi0S : i0 ∈ S := by rw [huniv]; exact Finset.mem_univ i0
    have hnotflat : ¬ ∀ i ∈ support p, p i = ((support p).card : ℝ)⁻¹ := by
      intro hflat
      exact hi0 (by rw [hflat i0 (by rw [← hS]; exact hi0S), ← hS, heqcard])
    have hne' : (∑ i, Real.negMulLog (p i)) ≠ Real.log (S.card : ℝ) := by
      intro h
      exact hnotflat ((sum_negMulLog_eq_log_card_support_iff hp hsum).mp (by rw [hS] at *; exact h))
    have := lt_of_le_of_ne hbound hne'
    rw [heqcard] at this
    exact this
