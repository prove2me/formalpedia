-- Prove2me | solution 1 for IITTensorNetwork.sum_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:33:55.973756+00:00
-- url     : https://prove2.me/submissions/3af21f15-1bd0-438f-b00f-15c52f10f104

-- Sol generated from Novelty/IITTensorNetworkEntropy.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy

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
theorem solution(p : ι → ℝ) : ∑ i ∈ support p, p i = ∑ i, p i :=
  Finset.sum_subset (Finset.subset_univ _) (by
    intro i _ hi
    simpa [support] using hi)
