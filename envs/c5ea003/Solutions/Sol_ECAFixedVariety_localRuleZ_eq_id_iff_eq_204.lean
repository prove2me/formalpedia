-- Prove2me | solution 1 for ECAFixedVariety.localRuleZ_eq_id_iff_eq_204
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:02:23.707616+00:00
-- url     : https://prove2.me/submissions/5c824a3b-7525-4618-a1ed-2692dc7513d6

-- Sol generated from Novelty/ECAMaximalDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAPeriodicPointLattice
import Theorems.Thm_ECAFixedVariety_rule204_localRuleZ

/-!
# Cycle 3: maximal dimension forces the identity automaton

The conjecture predicts that the Turing-complete class-4 rules have fixed-point
variety of maximal dimension `n`.  Cycles 1–2 showed Rule 110 has dimension `0`.
Here we close the question completely by classifying *which* elementary rules can
have a maximal-dimensional fixed-point variety: **exactly one, the identity Rule
204**, whose dynamics is trivial.

## Main results

* `exists_cfg_window` — on a ring of size `n ≥ 3` every `3`-cell window can be
  prescribed independently: the fixed-point equations really are `n` independent
  cubic equations.
* `fixedSet_eq_univ_iff` — the variety is all of `𝔸ⁿ` iff the local rule is the
  centre projection.
* `localRuleZ_eq_id_iff_eq_204` — for a genuine Wolfram number (`rule < 256`)
  that happens iff the rule is `204`.
* `hasFixedDim_max_iff` / `hasFixedDim_max_iff_eq_204` — **maximal dimension
  characterises the identity automaton**.  In particular the `255`
  non-identity rules, Rule 110 included, all fail the conjecture's class-4
  prediction, while the unique rule that satisfies it is the most trivial one in
  the whole family.
-/

open ECAFixedVariety









open ECAFixedVariety in
theorem solution{rule : ℕ} (hrule : rule < 256) :
    (∀ l c r : ZMod 2, localRuleZ rule l c r = c) ↔ rule = 204 := by
  constructor
  · intro h
    -- read off the eight bits of the truth table
    have bit : ∀ l c r : ZMod 2,
        rule.testBit (4 * l.val + 2 * c.val + r.val) = decide (c = 1) := by
      intro l c r
      have hlc := h l c r
      rw [localRuleZ] at hlc
      by_cases hbit : rule.testBit (4 * l.val + 2 * c.val + r.val) = true
      · rw [if_pos hbit] at hlc
        rw [hbit, ← hlc]
        decide
      · rw [if_neg hbit] at hlc
        rw [Bool.not_eq_true] at hbit
        rw [hbit, ← hlc]
        decide
    refine Nat.eq_of_testBit_eq (fun j => ?_)
    rcases lt_or_ge j 8 with hj | hj
    · interval_cases j
      · simpa using bit 0 0 0
      · simpa using bit 0 0 1
      · simpa using bit 0 1 0
      · simpa using bit 0 1 1
      · simpa using bit 1 0 0
      · simpa using bit 1 0 1
      · simpa using bit 1 1 0
      · simpa using bit 1 1 1
    · have h1 : rule.testBit j = false := by
        apply Nat.testBit_lt_two_pow
        calc rule < 256 := hrule
          _ = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      have h2 : (204 : ℕ).testBit j = false := by
        apply Nat.testBit_lt_two_pow
        calc (204 : ℕ) < 2 ^ 8 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      rw [h1, h2]
  · rintro rfl
    exact rule204_localRuleZ
