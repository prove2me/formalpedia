-- Prove2me | solution 1 for IITTensorNetwork.vnEntropy_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:48:36.233348+00:00
-- url     : https://prove2.me/submissions/09a21333-cbf7-41ce-b959-fba2b6f28509

-- Sol generated from Novelty/IITTensorNetworkEntropy.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_IITTensorNetwork_vnEntropy_of_isHermitian

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
/-- A real scalar multiple of the identity matrix is Hermitian. -/
lemma isHermitian_real_smul_one (c : ℝ) : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  norm_num [Complex.star_def]

/-- Eigenvalues of a scalar matrix `c • 1` are all equal to `c`. -/
lemma eigenvalues_smul_one {c : ℝ} (hc : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) (i : n) :
    hc.eigenvalues i = c := by
  have h := hc.eigenvalues_eq i
  have hmv : ((c : ℂ) • (1 : Matrix n n ℂ)) *ᵥ (hc.eigenvectorBasis i).ofLp
      = (c : ℂ) • (hc.eigenvectorBasis i).ofLp := by
    simp [Matrix.smul_mulVec]
  have hnorm : star ((hc.eigenvectorBasis i).ofLp) ⬝ᵥ ((hc.eigenvectorBasis i).ofLp) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [inner_self_eq_norm_sq_to_K, hc.eigenvectorBasis.orthonormal.1 i]
  rw [hmv, dotProduct_smul, hnorm] at h
  simpa using h








open IITTensorNetwork in
theorem solution(c : ℝ) :
    vnEntropy ((c : ℂ) • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) * Real.negMulLog c := by
  have hherm : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := isHermitian_real_smul_one c
  rw [vnEntropy_of_isHermitian hherm]
  simp [eigenvalues_smul_one hherm, Finset.card_univ]
