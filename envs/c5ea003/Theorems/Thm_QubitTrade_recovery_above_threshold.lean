-- Prove2me | Theorems.Thm_QubitTrade_recovery_above_threshold
-- name    : QubitTrade.recovery_above_threshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:52:48.134578+00:00
-- url     : https://prove2.me/theorems/dd54a917-bad9-4478-9042-aa10149076eb
-- title:
--   Honest post-processing recovers the order above the threshold.
-- statement:
--   **Honest post-processing recovers the order above the threshold.**
--
--   Assume the register satisfies `R^2 ≤ 2^t`, the true order `r ≤ R`, and that for
--   every sample `k` of the record the post-processor returns *some* fraction `q k` of
--   reduced denominator `≤ R` compatible with the same observed phase as the true
--   fraction `k/r`.  If the sampled numerators are jointly coprime to `r`, then the
--   least common multiple of the returned denominators is exactly `r`.
--
--   ```lean
--   theorem QubitTrade.recovery_above_threshold{R t r : ℕ} (hRt : ((R : ℝ)) ^ 2 ≤ 2 ^ t)
--       (hr : 0 < r) (hrR : r ≤ R) {ks : List ℕ} (hgcd : Nat.gcd (recordGcd ks) r = 1)
--       (q : ℕ → ℚ)
--       (hq : ∀ k ∈ ks, (q k).den ≤ R ∧
--         ∃ x : ℝ, Compatible t x (orderFrac k r) ∧ Compatible t x (q k)) :
--       (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Threshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Threshold.lean#L97

-- Thm stub generated from Algebra/QubitTrade/Threshold.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SupportCollapse

/-!
# QUBIT-TRADE IV: synthesis — the register size is forced

This file packages the three halves of the experiment into bit-counted statements
and one end-to-end recovery theorem.

* `QubitTrade.register_suffices` — `t ≥ 2 log₂ R + 2` determines the
  continued-fraction target;
* `QubitTrade.register_fails` — `t + 1 ≤ 2 log₂ R` (and `R ≥ 3`) leaves it
  ambiguous;
* `QubitTrade.register_threshold_bits` — the two together: the minimal register
  size obeys `2 log₂ R - 1 ≤ t_min ≤ 2 log₂ R + 2`, i.e. `t_min = 2 log₂ R + O(1)`
  and **not** `log₂ R + O(log log R)`;
* `QubitTrade.recovery_above_threshold` — above the threshold, honest continued
  fraction post-processing of a record whose numerators are jointly coprime to
  the order returns the order *exactly*: qubits above `2 log₂ R` plus samples
  compensating `gcd (k, r) > 1`;
* `QubitTrade.qubit_trade_trichotomy` — the three regimes in a single statement.

Reading it with `r ~ N` (the generic case for a random base modulo a semiprime)
gives `t_min ≈ 2 log₂ N`, which is Shor's full register: the quantum channel
cannot be shrunk by truncation.
-/

open QubitTrade

open Nat

/-! ## Bit-counted forms of the threshold -/




/-! ## End-to-end recovery above the threshold -/

theorem QubitTrade.recovery_above_threshold{R t r : ℕ} (hRt : ((R : ℝ)) ^ 2 ≤ 2 ^ t)
    (hr : 0 < r) (hrR : r ≤ R) {ks : List ℕ} (hgcd : Nat.gcd (recordGcd ks) r = 1)
    (q : ℕ → ℚ)
    (hq : ∀ k ∈ ks, (q k).den ≤ R ∧
      ∃ x : ℝ, Compatible t x (orderFrac k r) ∧ Compatible t x (q k)) :
    (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r := by sorry
