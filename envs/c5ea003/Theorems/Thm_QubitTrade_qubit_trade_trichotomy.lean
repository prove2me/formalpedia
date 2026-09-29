-- Prove2me | Theorems.Thm_QubitTrade_qubit_trade_trichotomy
-- name    : QubitTrade.qubit_trade_trichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:53:03.711189+00:00
-- url     : https://prove2.me/theorems/4e4f8929-e45e-4c35-8abf-2cd1ba3998be
-- title:
--   The qubit ↔ sample trade, in one statement.
-- statement:
--   **The qubit ↔ sample trade, in one statement.**  Fix an order bound `R ≥ 3`.
--
--   1. *Collapse* (`t ≤ log₂ r`): if two distinct orders both exceed `2^t`, no
--      estimator using **any** number of truncated samples can be correct for both.
--   2. *Single-shot ambiguity* (`t < 2 log₂ R`): the continued-fraction target itself
--      is not determined by a `t`-bit phase.
--   3. *Recovery* (`t ≥ 2 log₂ R + 2`): the target is determined, and a record of
--      samples jointly coprime to the order returns the order exactly.
--
--   Samples are fungible with qubits only in regime 3, where they repair
--   `gcd (k, r) > 1`; in regimes 1–2 they buy nothing.
--
--   ```lean
--   theorem QubitTrade.qubit_trade_trichotomy{R : ℕ} (hR : 3 ≤ R) :
--       (∀ (t r r' : ℕ), 2 ^ t ≤ r → 2 ^ t ≤ r' → r ≠ r' → ∀ A : List ℕ → ℕ,
--           ¬ ((∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r) → A L = r) ∧
--              (∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r') → A L = r'))) ∧
--       (∀ t : ℕ, t + 1 ≤ 2 * Nat.log 2 R →
--           ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
--             Compatible t x q₁ ∧ Compatible t x q₂) ∧
--       (∀ (t r : ℕ), 2 * Nat.log 2 R + 2 ≤ t → 0 < r → r ≤ R → ∀ ks : List ℕ,
--           Nat.gcd (recordGcd ks) r = 1 → ∀ q : ℕ → ℚ,
--           (∀ k ∈ ks, (q k).den ≤ R ∧
--             ∃ x : ℝ, Compatible t x (orderFrac k r) ∧ Compatible t x (q k)) →
--           (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Threshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Threshold.lean#L126

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


/-! ## The three regimes -/

theorem QubitTrade.qubit_trade_trichotomy{R : ℕ} (hR : 3 ≤ R) :
    (∀ (t r r' : ℕ), 2 ^ t ≤ r → 2 ^ t ≤ r' → r ≠ r' → ∀ A : List ℕ → ℕ,
        ¬ ((∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r) → A L = r) ∧
           (∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r') → A L = r'))) ∧
    (∀ t : ℕ, t + 1 ≤ 2 * Nat.log 2 R →
        ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
          Compatible t x q₁ ∧ Compatible t x q₂) ∧
    (∀ (t r : ℕ), 2 * Nat.log 2 R + 2 ≤ t → 0 < r → r ≤ R → ∀ ks : List ℕ,
        Nat.gcd (recordGcd ks) r = 1 → ∀ q : ℕ → ℚ,
        (∀ k ∈ ks, (q k).den ≤ R ∧
          ∃ x : ℝ, Compatible t x (orderFrac k r) ∧ Compatible t x (q k)) →
        (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r) := by sorry
