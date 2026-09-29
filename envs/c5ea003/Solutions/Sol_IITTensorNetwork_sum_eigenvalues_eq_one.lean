-- Prove2me | solution 1 for IITTensorNetwork.sum_eigenvalues_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:46:05.610759+00:00
-- url     : https://prove2.me/submissions/aea9bb10-205b-4af6-ae0d-31eaac8233a6

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
theorem solution{A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, hA.isHermitian.eigenvalues i = 1 := by
  have h := hA.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  have : ((∑ i, hA.isHermitian.eigenvalues i : ℝ) : ℂ) = (1 : ℂ) := by
    push_cast
    exact h.symm
  exact_mod_cast this
