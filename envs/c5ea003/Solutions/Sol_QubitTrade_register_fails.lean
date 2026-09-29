-- Prove2me | solution 1 for QubitTrade.register_fails
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:54:27.870534+00:00
-- url     : https://prove2.me/submissions/665c085e-46bb-4f52-9f54-05fdb50c5e66

-- Sol generated from Algebra/QubitTrade/Threshold.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_cf_target_ambiguous

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
theorem solution{R t : ℕ} (hR : 3 ≤ R) (ht : t + 1 ≤ 2 * Nat.log 2 R) :
    ∃ (x : ℝ) (q₁ q₂ : ℚ), q₁ ≠ q₂ ∧ q₁.den ≤ R ∧ q₂.den ≤ R ∧
      Compatible t x q₁ ∧ Compatible t x q₂ := by
  have hRpos : (0:ℝ) < R := by
    have : (0:ℕ) < R := by omega
    exact_mod_cast this
  have hR3 : (3:ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hlog : ((2 ^ Nat.log 2 R : ℕ) : ℝ) ≤ (R : ℝ) := by
    have := Nat.pow_log_le_self 2 (x := R) (by omega : R ≠ 0)
    exact_mod_cast this
  have hlogpow : ((2:ℝ)) ^ Nat.log 2 R ≤ (R : ℝ) := by push_cast at hlog; exact hlog
  have hstep : ((2:ℝ)) ^ (t + 1) ≤ (R : ℝ) ^ 2 := by
    calc ((2:ℝ)) ^ (t + 1) ≤ (2:ℝ) ^ (2 * Nat.log 2 R) := by
          apply pow_le_pow_right₀ (by norm_num) ht
      _ = ((2:ℝ) ^ Nat.log 2 R) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ (R : ℝ) ^ 2 := by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (Nat.log 2 R)]
  have hkey : ((2:ℝ)) ^ t < (R : ℝ) * ((R : ℝ) - 1) := by
    have h2 : ((2:ℝ)) ^ (t + 1) = 2 * (2:ℝ) ^ t := by rw [pow_succ]; ring
    nlinarith
  obtain ⟨x, hne, hd₁, hd₂, c₁, c₂⟩ := cf_target_ambiguous (by omega : 2 ≤ R) hkey
  exact ⟨x, orderFrac 1 R, orderFrac 1 (R - 1), hne, by omega, by omega, c₁, c₂⟩
