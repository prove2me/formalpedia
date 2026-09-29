-- Prove2me | solution 1 for IITTensorNetwork.vnEntropy_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:05:23.424972+00:00
-- url     : https://prove2.me/submissions/2d0b6b0a-f111-4790-bfb4-5f6aad50b2c0

-- Sol generated from Novelty/IITTensorNetworkEntropy.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_IITTensorNetwork_roots_charpoly_diagonal
import Theorems.Thm_IITTensorNetwork_vnEntropy_eq_multiset_sum

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











omit [Fintype n] in
/-- A diagonal matrix with real entries is Hermitian. -/
lemma isHermitian_diagonal_real (v : n → ℝ) :
    (Matrix.diagonal (fun i => (v i : ℂ))).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  simp






open IITTensorNetwork in
theorem solution(v : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (v i : ℂ))) = ∑ i, Real.negMulLog (v i) := by
  rw [vnEntropy_eq_multiset_sum (isHermitian_diagonal_real v), roots_charpoly_diagonal,
    Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  simp
