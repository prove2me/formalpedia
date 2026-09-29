-- Prove2me | Theorems.Thm_IITTensorNetwork_vnEntropy_smul_one
-- name    : IITTensorNetwork.vnEntropy_smul_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:25:05.826363+00:00
-- url     : https://prove2.me/theorems/49d738b1-c21f-4a33-9946-bbf8646ea43f
-- title:
--   The entropy of a maximally mixed spectrum: `S(c • 1) = |n| · (-c log c)`.
-- statement:
--   The entropy of a maximally mixed spectrum: `S(c • 1) = |n| · (-c log c)`.
--
--   ```lean
--   theorem IITTensorNetwork.vnEntropy_smul_one(c : ℝ) :
--       vnEntropy ((c : ℂ) • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) * Real.negMulLog c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEntropy.lean#L275

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

theorem IITTensorNetwork.vnEntropy_smul_one(c : ℝ) :
    vnEntropy ((c : ℂ) • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) * Real.negMulLog c := by sorry
