-- Prove2me | solution 1 for IITTensorNetwork.sum_negMulLog_le_log_card_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:38:56.451468+00:00
-- url     : https://prove2.me/submissions/dad9c914-b0f0-4d3c-857c-69dfd8612072

-- Sol generated from Novelty/IITTensorNetworkEntropy.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_IITTensorNetwork_mem_support
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_support
import Theorems.Thm_IITTensorNetwork_sum_support
import Theorems.Thm_IITTensorNetwork_support_nonempty

/-! # Entropy toolkit for integrated information of tensor network states

This file provides the entropic infrastructure used by the formalization of
Tononi's Integrated Information Theory (IIT) in terms of tensor network states.

We work with Shannon entropy of a finite probability vector and with the von
Neumann entropy of a Hermitian complex matrix, defined through the eigenvalues
supplied by Mathlib's spectral theorem.  The main results are

* `sum_negMulLog_le_log_card_support` : Shannon entropy is bounded by the
  logarithm of the size of the support (the "maximal entropy" bound);
* `sum_negMulLog_eq_zero_iff` : entropy vanishes exactly for point masses;
* `vnEntropy_le_log_rank` : von Neumann entropy of a positive semidefinite
  matrix of unit trace is at most the logarithm of its rank;
* `vnEntropy_eq_zero_iff_rank_eq_one` : the von Neumann entropy vanishes iff the
  state is pure (rank one);
* `vnEntropy_smul_one` : the entropy of a flat (maximally mixed) spectrum.
-/

open Finset

open IITTensorNetwork

/-! ## Shannon entropy of a finite probability vector -/


variable {ι : Type*} [Fintype ι]










/-! ## Von Neumann entropy of a Hermitian matrix -/


variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix
open scoped ComplexOrder

















open IITTensorNetwork in
theorem solution{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (support p).card := by
  set S := support p with hS
  set r : ℝ := (S.card : ℝ) with hr
  have hSne : S.Nonempty := support_nonempty hsum
  have hrpos : 0 < r := by
    rw [hr]
    exact_mod_cast Finset.card_pos.mpr hSne
  have hsumS : ∑ i ∈ S, p i = 1 := by rw [sum_support p, hsum]
  have key : ∀ i ∈ S, Real.negMulLog (p i) ≤ p i * Real.log r + 1 / r - p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (mem_support.mp hi))
    have hx : 0 < 1 / (r * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    have hmul : p i * Real.log (1 / (r * p i)) ≤ p i * (1 / (r * p i) - 1) :=
      mul_le_mul_of_nonneg_left hlog hpi.le
    have hrewrite : Real.log (1 / (r * p i)) = -(Real.log r + Real.log (p i)) := by
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (ne_of_gt hrpos) (ne_of_gt hpi)]
      ring
    have hval : p i * (1 / (r * p i) - 1) = 1 / r - p i := by
      field_simp
    rw [hrewrite, hval] at hmul
    have hexp : p i * (-(Real.log r + Real.log (p i)))
        = -(p i * Real.log r) - p i * Real.log (p i) := by ring
    rw [hexp] at hmul
    simp only [Real.negMulLog]
    nlinarith [hmul]
  calc ∑ i, Real.negMulLog (p i) = ∑ i ∈ S, Real.negMulLog (p i) :=
        (sum_negMulLog_support p).symm
    _ ≤ ∑ i ∈ S, (p i * Real.log r + 1 / r - p i) := Finset.sum_le_sum key
    _ = (∑ i ∈ S, p i) * Real.log r + S.card * (1 / r) - ∑ i ∈ S, p i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
          Finset.sum_const, nsmul_eq_mul]
    _ = Real.log r := by
        rw [hsumS, ← hr]
        field_simp
        ring
