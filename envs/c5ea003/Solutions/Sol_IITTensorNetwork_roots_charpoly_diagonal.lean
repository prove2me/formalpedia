-- Prove2me | solution 1 for IITTensorNetwork.roots_charpoly_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:02:16.111117+00:00
-- url     : https://prove2.me/submissions/b431416b-c455-41b8-8cf4-990491ddab30

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
theorem solution(v : n → ℂ) :
    (Matrix.diagonal v).charpoly.roots = Multiset.map v Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
  rw [show (Multiset.map (fun i => Polynomial.X - Polynomial.C (v i)) Finset.univ.val)
      = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map v Finset.univ.val) by rw [Multiset.map_map]; rfl]
  exact Polynomial.roots_multiset_prod_X_sub_C _
