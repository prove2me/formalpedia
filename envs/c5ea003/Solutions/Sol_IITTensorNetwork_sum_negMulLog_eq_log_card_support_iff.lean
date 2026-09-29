-- Prove2me | solution 1 for IITTensorNetwork.sum_negMulLog_eq_log_card_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:43:37.20857+00:00
-- url     : https://prove2.me/submissions/ce8d5338-8e6f-4fce-b4de-14af4c71df8c

-- Sol generated from Novelty/IITTensorNetworkEquality.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Theorems.Thm_IITTensorNetwork_mem_support
import Theorems.Thm_IITTensorNetwork_negMulLog_le_flat_bound
import Theorems.Thm_IITTensorNetwork_negMulLog_lt_flat_bound
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_support
import Theorems.Thm_IITTensorNetwork_sum_support
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



/-- The Shannon entropy of a vector that is uniform on its support is exactly
the logarithm of the size of the support. -/
theorem sum_negMulLog_of_flat {p : ι → ℝ} (hsum : ∑ i, p i = 1)
    (hflat : ∀ i ∈ support p, p i = ((support p).card : ℝ)⁻¹) :
    ∑ i, Real.negMulLog (p i) = Real.log (support p).card := by
  have hSne : (support p).Nonempty := support_nonempty hsum
  have hrpos : (0 : ℝ) < (support p).card := by
    exact_mod_cast Finset.card_pos.mpr hSne
  rw [← sum_negMulLog_support p]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hflat i hi])]
  rw [Finset.sum_const, nsmul_eq_mul, Real.negMulLog, Real.log_inv]
  field_simp




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
theorem solution{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) = Real.log (support p).card ↔
      ∀ i ∈ support p, p i = ((support p).card : ℝ)⁻¹ := by
  classical
  set S := support p with hS
  have hSne : S.Nonempty := support_nonempty hsum
  have hrpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
  have hsumS : ∑ i ∈ S, p i = 1 := by rw [hS, sum_support p, hsum]
  refine ⟨fun heq => ?_, fun hflat => sum_negMulLog_of_flat hsum hflat⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0S, hi0⟩ := hcon
  have hpi0 : 0 < p i0 := lt_of_le_of_ne (hp i0) (Ne.symm (mem_support.mp hi0S))
  have hi0' : p i0 ≠ 1 / (S.card : ℝ) := by
    rw [one_div]; exact hi0
  have hle : ∀ i ∈ S, Real.negMulLog (p i)
      ≤ p i * Real.log (S.card : ℝ) + 1 / (S.card : ℝ) - p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (mem_support.mp hi))
    exact negMulLog_le_flat_bound hrpos hpi
  have hlt : ∑ i ∈ S, Real.negMulLog (p i)
      < ∑ i ∈ S, (p i * Real.log (S.card : ℝ) + 1 / (S.card : ℝ) - p i) :=
    Finset.sum_lt_sum hle ⟨i0, hi0S, negMulLog_lt_flat_bound hrpos hpi0 hi0'⟩
  have hrhs : ∑ i ∈ S, (p i * Real.log (S.card : ℝ) + 1 / (S.card : ℝ) - p i)
      = Real.log (S.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_const, nsmul_eq_mul, hsumS]
    field_simp
    ring
  rw [hrhs] at hlt
  rw [← sum_negMulLog_support p, ← hS] at heq
  exact absurd heq (ne_of_lt hlt)
