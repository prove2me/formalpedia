-- Prove2me | solution 1 for QubitTrade.register_suffices
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:57.620543+00:00
-- url     : https://prove2.me/submissions/1031587b-69d8-49ed-949c-a522943908ba

-- Sol generated from Algebra/QubitTrade/Threshold.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_cf_target_unique

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
theorem solution{R t : ℕ} (hR : 1 ≤ R) (ht : 2 * Nat.log 2 R + 2 ≤ t)
    {x : ℝ} {q₁ q₂ : ℚ} (h₁ : q₁.den ≤ R) (h₂ : q₂.den ≤ R)
    (c₁ : Compatible t x q₁) (c₂ : Compatible t x q₂) : q₁ = q₂ := by
  refine cf_target_unique ?_ h₁ h₂ c₁ c₂
  have hlt : R < 2 ^ (Nat.log 2 R + 1) := Nat.lt_pow_succ_log_self (by norm_num) R
  have hltR : (R : ℝ) < ((2 ^ (Nat.log 2 R + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
  have hRnn : (0:ℝ) ≤ (R : ℝ) := by positivity
  have hsq : ((R : ℝ)) ^ 2 ≤ ((2:ℝ) ^ (Nat.log 2 R + 1)) ^ 2 := by
    have : (R : ℝ) ≤ (2:ℝ) ^ (Nat.log 2 R + 1) := by
      push_cast at hltR
      linarith
    nlinarith
  calc ((R : ℝ)) ^ 2 ≤ ((2:ℝ) ^ (Nat.log 2 R + 1)) ^ 2 := hsq
    _ = (2:ℝ) ^ (2 * Nat.log 2 R + 2) := by rw [← pow_mul]; ring_nf
    _ ≤ (2:ℝ) ^ t := by
        apply pow_le_pow_right₀ (by norm_num) ht
