-- Prove2me | solution 1 for IITTensorNetwork.support_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:36:31.256993+00:00
-- url     : https://prove2.me/submissions/c7995983-7b5f-463f-9769-783ff7cd515d

-- Sol generated from Novelty/IITTensorNetworkEntropy.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_IITTensorNetwork_sum_support

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
theorem solution{p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    (support p).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (support p) with h | h
  · exfalso
    have : ∑ i, p i = 0 := by
      rw [← sum_support p, h, Finset.sum_empty]
    rw [hsum] at this
    norm_num at this
  · exact h
