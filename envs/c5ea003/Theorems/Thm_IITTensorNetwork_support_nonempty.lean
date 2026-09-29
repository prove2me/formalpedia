-- Prove2me | Theorems.Thm_IITTensorNetwork_support_nonempty
-- name    : IITTensorNetwork.support_nonempty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:24:15.088925+00:00
-- url     : https://prove2.me/theorems/ab53242a-be35-4c74-b828-a544f24d5b35
-- title:
--   The support of a probability vector is nonempty.
-- statement:
--   The support of a probability vector is nonempty.
--
--   ```lean
--   theorem IITTensorNetwork.support_nonempty{p : ι → ℝ} (hsum : ∑ i, p i = 1) :
--       (support p).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkEntropy.lean#L50

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

theorem IITTensorNetwork.support_nonempty{p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    (support p).Nonempty := by sorry
