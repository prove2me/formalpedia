-- Prove2me | Theorems.Thm_IITTensorNetwork_roots_charpoly_diagonal
-- name    : IITTensorNetwork.roots_charpoly_diagonal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:59:06.315476+00:00
-- url     : https://prove2.me/theorems/a675d90c-07fd-4553-864b-55ea066157cc
-- title:
--   Characteristic roots of a diagonal matrix are its diagonal entries.
-- statement:
--   Characteristic roots of a diagonal matrix are its diagonal entries.
--
--   ```lean
--   theorem IITTensorNetwork.roots_charpoly_diagonal(v : n → ℂ) :
--       (Matrix.diagonal v).charpoly.roots = Multiset.map v Finset.univ.val := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEntropy.lean#L258

-- Thm stub generated from Novelty/IITTensorNetworkEntropy.lean
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

theorem IITTensorNetwork.roots_charpoly_diagonal(v : n → ℂ) :
    (Matrix.diagonal v).charpoly.roots = Multiset.map v Finset.univ.val := by sorry
