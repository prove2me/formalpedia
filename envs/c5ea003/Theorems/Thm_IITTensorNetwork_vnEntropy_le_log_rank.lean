-- Prove2me | Theorems.Thm_IITTensorNetwork_vnEntropy_le_log_rank
-- name    : IITTensorNetwork.vnEntropy_le_log_rank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:24:50.173626+00:00
-- url     : https://prove2.me/theorems/02f07045-ce0a-416a-96ea-ee79f676763c
-- title:
--   Maximal entropy bound for density matrices.
-- statement:
--   **Maximal entropy bound for density matrices.**  The von Neumann entropy of
--   a density matrix is at most the logarithm of its rank.
--
--   ```lean
--   theorem IITTensorNetwork.vnEntropy_le_log_rank{A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
--       vnEntropy A ≤ Real.log A.rank := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEntropy.lean#L209

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

theorem IITTensorNetwork.vnEntropy_le_log_rank{A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    vnEntropy A ≤ Real.log A.rank := by sorry
