-- Prove2me | solution 1 for IITTensorNetwork.sum_negMulLog_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:05:24.132058+00:00
-- url     : https://prove2.me/submissions/55d0799f-b1c5-4440-b73b-5dbb9ae3875c

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
theorem solution{p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) = 0 ↔ (support p).card = 1 := by
  classical
  have hle : ∀ i, p i ≤ 1 := by
    intro i
    exact hsum ▸ Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  constructor
  · intro h
    have hterm : ∀ i ∈ Finset.univ, Real.negMulLog (p i) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h
      intro i _
      exact Real.negMulLog_nonneg (hp i) (hle i)
    -- each probability is `0` or `1`
    have hzo : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      have hi := hterm i (Finset.mem_univ i)
      rcases eq_or_lt_of_le (hp i) with h0 | h0
      · exact Or.inl h0.symm
      · right
        have : Real.log (p i) = 0 := by
          have : -p i * Real.log (p i) = 0 := hi
          rcases mul_eq_zero.mp this with h1 | h1
          · exact absurd (by linarith [neg_eq_zero.mp h1] : p i = 0) (ne_of_gt h0)
          · exact h1
        exact Real.eq_one_of_pos_of_log_eq_zero h0 this
    obtain ⟨i0, hi0⟩ := support_nonempty hsum
    have hone : p i0 = 1 := (hzo i0).resolve_left (mem_support.mp hi0)
    have hsupp : support p = {i0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi0, ?_⟩
      intro j hj
      by_contra hne
      have hj1 : p j = 1 := (hzo j).resolve_left (mem_support.mp hj)
      have : (2 : ℝ) ≤ ∑ i, p i := by
        have hsub : ({i0, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
        have : p i0 + p j ≤ ∑ i, p i := by
          have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hp i)
          simpa [Finset.sum_pair (Ne.symm hne), hone, hj1] using this
        rw [hone, hj1] at this
        linarith
      rw [hsum] at this
      linarith
    rw [hsupp, Finset.card_singleton]
  · intro h
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h
    have hone : p i0 = 1 := by
      have : ∑ i ∈ support p, p i = 1 := by rw [sum_support p, hsum]
      rwa [hi0, Finset.sum_singleton] at this
    have : ∑ i, Real.negMulLog (p i) = ∑ i ∈ support p, Real.negMulLog (p i) :=
      (sum_negMulLog_support p).symm
    rw [this, hi0, Finset.sum_singleton, hone, Real.negMulLog_one]
