-- Prove2me | Theorems.Thm_QubitTrade_register_fails
-- name    : QubitTrade.register_fails
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:53:13.352124+00:00
-- url     : https://prove2.me/theorems/f82d6f08-b3d7-4809-8f59-e30e5555255a
-- title:
--   A register of fewer than `2 log₂ R` bits does not: two distinct reduced
-- statement:
--   A register of fewer than `2 log₂ R` bits does **not**: two distinct reduced
--   fractions with denominators `≤ R` — realised by the two orders `R` and `R-1` —
--   remain compatible with a single phase.
--
--   ```lean
--   theorem QubitTrade.register_fails{R t : ℕ} (hR : 3 ≤ R) (ht : t + 1 ≤ 2 * Nat.log 2 R) :
--       ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
--         Compatible t x q₁ ∧ Compatible t x q₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Threshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Threshold.lean#L54

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

theorem QubitTrade.register_fails{R t : ℕ} (hR : 3 ≤ R) (ht : t + 1 ≤ 2 * Nat.log 2 R) :
    ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
      Compatible t x q₁ ∧ Compatible t x q₂ := by sorry
