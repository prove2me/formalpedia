-- Prove2me | Theorems.Thm_IITTensorNetwork_sum_eigenvalues_eq_one
-- name    : IITTensorNetwork.sum_eigenvalues_eq_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:24:54.041868+00:00
-- url     : https://prove2.me/theorems/383ebebe-9e1d-4bc3-877f-5e4ca07fa5d2
-- title:
--   Eigenvalues of a positive semidefinite matrix of unit trace form a
-- statement:
--   Eigenvalues of a positive semidefinite matrix of unit trace form a
--   probability vector.
--
--   ```lean
--   theorem IITTensorNetwork.sum_eigenvalues_eq_one{A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
--       ∑ i, hA.isHermitian.eigenvalues i = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEntropy.lean#L183

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

theorem IITTensorNetwork.sum_eigenvalues_eq_one{A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, hA.isHermitian.eigenvalues i = 1 := by sorry
