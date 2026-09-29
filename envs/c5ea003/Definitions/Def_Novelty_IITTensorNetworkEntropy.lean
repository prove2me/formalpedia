-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkEntropy
-- name    : Novelty_IITTensorNetworkEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:11.599879+00:00
-- url     : https://prove2.me/theorems/1911ed99-9a1a-4a2f-b533-50abe3ebf4ef
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkEntropy.lean by skeleton subtraction
import Mathlib

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

namespace IITTensorNetwork

/-! ## Shannon entropy of a finite probability vector -/

section Shannon

variable {ι : Type*} [Fintype ι]

/-- The support of a probability vector. -/
noncomputable def support (p : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => p i ≠ 0)








end Shannon

/-! ## Von Neumann entropy of a Hermitian matrix -/

section VonNeumann

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix
open scoped ComplexOrder

/-- The von Neumann entropy of a matrix: the Shannon entropy of its spectrum
when the matrix is Hermitian, and `0` otherwise. -/
noncomputable def vnEntropy (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0














end VonNeumann

end IITTensorNetwork


