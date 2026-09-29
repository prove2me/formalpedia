-- Prove2me | Theorems.Thm_sorted_identity_minimizes
-- name    : sorted_identity_minimizes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:27.329713+00:00
-- url     : https://prove2.me/theorems/3d1ea581-d2fa-442b-bfeb-219a6438a654
-- title:
--   Sorted identity minimizes
-- statement:
--   Formal statement of `sorted_identity_minimizes` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem sorted_identity_minimizes{n : ℕ} (x y : Fin n → ℤ)
--       (hx : Monotone x) (hy : Monotone y) (σ : Equiv.Perm (Fin n)) :
--       ∑ i : Fin n, Int.natAbs (x i - y i) ≤
--       ∑ i : Fin n, Int.natAbs (x i - y (σ i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VoiceLeadingMonge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VoiceLeadingMonge.lean#L37

-- Thm stub generated from Bridges/VoiceLeadingMonge.lean
import Mathlib
/-
# The Monge Uncrossing Lemma and Sorted Matching Optimality

This file proves the discrete rearrangement inequality for absolute value on ℤ:
for monotone sequences, sorted (identity) matching minimizes the total absolute
difference over all permutations.

## Main Results

* `abs_monge` — The four-point Monge inequality for |·| on ℤ.
* `sorted_identity_minimizes` — For monotone sequences, the identity permutation
  minimizes the sum of coordinatewise absolute differences.
-/


open Finset Equiv

/-! ## The Monge Inequality -/


/-! ## Main Theorem: Sorted Identity Minimizes Cost -/

set_option maxHeartbeats 800000 in

/-
**Rearrangement Theorem for ℤ.** For monotone (sorted) sequences x and y,
    the identity matching minimizes the sum of absolute differences over all
    permutations. This is the discrete 1D optimal transport theorem.
-/

theorem sorted_identity_minimizes{n : ℕ} (x y : Fin n → ℤ)
    (hx : Monotone x) (hy : Monotone y) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, Int.natAbs (x i - y i) ≤
    ∑ i : Fin n, Int.natAbs (x i - y (σ i)) := by sorry
