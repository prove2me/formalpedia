-- Prove2me | Theorems.Thm_QubitTrade_sample_count_lower_bound
-- name    : QubitTrade.sample_count_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:53:32.395791+00:00
-- url     : https://prove2.me/theorems/3c499f55-cf0e-484a-9632-11c57bae3d58
-- title:
--   Counting bound on truncated samples.
-- statement:
--   **Counting bound on truncated samples.**  Suppose that for each order `r` in a
--   finite family `S` there is a record `L r` of exactly `m` symbols of the `t`-bit
--   alphabet on which the estimator `A` answers `r`.  Then `|S| ≤ (2^t)^m`: the total
--   number of extracted bits `m · t` is at least `log₂ |S|`.
--
--   ```lean
--   theorem QubitTrade.sample_count_lower_bound{t m : ℕ} (S : Finset ℕ) (A : List ℕ → ℕ) (L : ℕ → List ℕ)
--       (hlen : ∀ r ∈ S, (L r).length = m) (halph : ∀ r ∈ S, ∀ x ∈ L r, x < 2 ^ t)
--       (hA : ∀ r ∈ S, A (L r) = r) :
--       S.card ≤ (2 ^ t) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/SampleComplexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/SampleComplexity.lean#L28

-- Thm stub generated from Algebra/QubitTrade/SampleComplexity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Capacity

/-!
# QUBIT-TRADE VII: the exchange rate between qubits and samples

`Capacity.lean` shows that one truncated sample carries at most `t` bits (its
alphabet has `min (2^t) r` symbols).  Here we turn that into a *counting* lower
bound on the number of samples, which is the precise form of the observed
"qubit ↔ sample fungibility":

* `QubitTrade.sample_count_lower_bound` — if an estimator identifies every order
  in a family `S` from a record of `m` truncated samples, then `|S| ≤ (2^t)^m`,
  i.e. `m · t ≥ log₂ |S|`;
* `QubitTrade.sample_count_lower_bound_window` — applied to the collapse window
  `[2^t, R]` of `SupportCollapse.lean`: identifying an order below `R` costs
  `m · t ≥ log₂ (R - 2^t + 1)` — qubits and samples are exchangeable only through
  their *product*, never below the resolution threshold, where the right-hand side
  can never be met because the records themselves coincide.

The bound is unconditional and holds for arbitrary (even non-uniform,
computationally unbounded) post-processing.
-/

open QubitTrade

open Finset

theorem QubitTrade.sample_count_lower_bound{t m : ℕ} (S : Finset ℕ) (A : List ℕ → ℕ) (L : ℕ → List ℕ)
    (hlen : ∀ r ∈ S, (L r).length = m) (halph : ∀ r ∈ S, ∀ x ∈ L r, x < 2 ^ t)
    (hA : ∀ r ∈ S, A (L r) = r) :
    S.card ≤ (2 ^ t) ^ m := by sorry
