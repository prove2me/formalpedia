-- Prove2me | solution 1 for QubitTrade.qubit_trade_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:57.093842+00:00
-- url     : https://prove2.me/submissions/c6a2e1a3-b5df-40e5-b741-df05deb2d95d

-- Sol generated from Algebra/QubitTrade/Threshold.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_recovery_above_threshold
import Theorems.Thm_QubitTrade_register_fails
import Theorems.Thm_QubitTrade_samples_do_not_help

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



open QubitTrade in
theorem solution{R : ℕ} (hR : 3 ≤ R) :
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
        (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r) := by
  refine ⟨fun t r r' h h' hne A => samples_do_not_help h h' hne A,
          fun t ht => register_fails hR ht, fun t r ht hr hrR ks hgcd q hq => ?_⟩
  refine recovery_above_threshold ?_ hr hrR hgcd q hq
  -- the bit hypothesis implies the arithmetic one
  have hlt : R < 2 ^ (Nat.log 2 R + 1) := Nat.lt_pow_succ_log_self (by norm_num) R
  have hltR : (R : ℝ) ≤ (2:ℝ) ^ (Nat.log 2 R + 1) := by
    have : (R : ℝ) < ((2 ^ (Nat.log 2 R + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this
    linarith
  have hRnn : (0:ℝ) ≤ (R : ℝ) := by positivity
  calc ((R : ℝ)) ^ 2 ≤ ((2:ℝ) ^ (Nat.log 2 R + 1)) ^ 2 := by nlinarith
    _ = (2:ℝ) ^ (2 * Nat.log 2 R + 2) := by rw [← pow_mul]; ring_nf
    _ ≤ (2:ℝ) ^ t := pow_le_pow_right₀ (by norm_num) ht
