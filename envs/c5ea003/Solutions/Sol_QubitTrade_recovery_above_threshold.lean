-- Prove2me | solution 1 for QubitTrade.recovery_above_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:54:27.330972+00:00
-- url     : https://prove2.me/submissions/afdc03fa-19df-4529-9ffa-fe3521f02c62

-- Sol generated from Algebra/QubitTrade/Threshold.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_cf_target_unique
import Theorems.Thm_QubitTrade_orderFrac_den
import Theorems.Thm_QubitTrade_samples_recover

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
theorem solution{R t r : ℕ} (hRt : ((R : ℝ)) ^ 2 ≤ 2 ^ t)
    (hr : 0 < r) (hrR : r ≤ R) {ks : List ℕ} (hgcd : Nat.gcd (recordGcd ks) r = 1)
    (q : ℕ → ℚ)
    (hq : ∀ k ∈ ks, (q k).den ≤ R ∧
      ∃ x : ℝ, Compatible t x (orderFrac k r) ∧ Compatible t x (q k)) :
    (ks.map (fun k => (q k).den)).foldr Nat.lcm 1 = r := by
  have hden : ∀ k ∈ ks, (q k).den = recovered k r := by
    intro k hk
    obtain ⟨hb, x, hx₁, hx₂⟩ := hq k hk
    have htrue : (orderFrac k r).den ≤ R := by
      rw [orderFrac_den k r hr]
      exact le_trans (Nat.div_le_self _ _) hrR
    have := cf_target_unique hRt htrue hb hx₁ hx₂
    rw [← this]
    rfl
  have hmap : ks.map (fun k => (q k).den) = ks.map (fun k => recovered k r) :=
    List.map_congr_left hden
  rw [hmap]
  exact samples_recover hr hgcd
