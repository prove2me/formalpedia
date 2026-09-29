-- Prove2me | solution 1 for ECAFixedVariety.rule90_eq_zero_of_two_zeros
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:21:49.803057+00:00
-- url     : https://prove2.me/submissions/6eb175ac-59a9-4b8f-bef7-90be3902ee5a

-- Sol generated from Novelty/ECAFixedVarietyPeriodThree.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff

/-!
# Period-three rigidity: the fixed-point variety depends on `n mod 3`

Wolfram's classification assigns a **single** class to a rule, independently of
the ring size `n`.  We show that the fixed-point variety cannot possibly encode
such an `n`-independent invariant, because for two of the most-studied rules —
the additive Rule 90 and the chaotic Rule 45 (both Wolfram class 3) — the
variety is governed by the arithmetic of `n mod 3`:

* `rule90_period_three`, `rule45_period_three` — every stationary configuration
  of Rule 90 or Rule 45 is invariant under the shift by `3`.
* `rule90_fixedSet_eq_zero_of_not_three_dvd` — if `3 ∤ n` then Rule 90 has only
  the zero configuration: dimension `0`.
* `rule90_exists_nonzero_fixed_of_three_dvd` — if `3 ∣ n` (and `n ≠ 0`) the
  variety is strictly bigger: it contains the `3`-periodic wave `011011…`.
* `rule90_hasFixedDim_le_two` — but it never exceeds dimension `2`; in
  particular `rule90_dim_lt_half`, so a class-3 rule violates the predicted
  `dim ≥ n/2` for all `n ≥ 5`.
* `rule45_fixedSet_empty_of_not_three_dvd` — the class-3 Rule 45 has an
  **empty** fixed-point variety when `3 ∤ n`, so no dimension is even definable.
* `rule45_exists_fixed_of_three_dvd` — while for `3 ∣ n` it is non-empty.

The common mechanism is the *transfer relation* of the fixed-point subshift: for
both rules two (resp. three) consecutive stationarity constraints force
`s_{i+3} = s_i`, and when `3` is invertible in `ZMod n` this collapses the whole
configuration to a constant, which the local rule then pins down.
-/

open ECAFixedVariety

/-! ### Consequences of shift-by-three invariance -/


/-! ### Rule 90 -/

/-- Rule 90 is the additive rule `l + r`. -/
lemma rule90_local_iff : ∀ l c r : ZMod 2, localRuleZ 90 l c r = c ↔ l + r = c := by decide









/-! ### Rule 45 -/







open ECAFixedVariety in
theorem solution{n : ℕ} [NeZero n] {s : Cfg n}
    (hs : s ∈ fixedSet 90 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by
  rw [mem_fixedSet_iff] at hs
  have key : ∀ k : ℕ, s ((k : ℕ) : ZMod n) = 0 ∧ s (((k + 1 : ℕ) : ℕ) : ZMod n) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1⟩
    | succ m ih =>
        obtain ⟨hm, hm1⟩ := ih
        refine ⟨by simpa using hm1, ?_⟩
        have hcon := hs (((m + 1 : ℕ) : ZMod n))
        rw [rule90_local_iff] at hcon
        have e1 : ((m + 1 : ℕ) : ZMod n) - 1 = ((m : ℕ) : ZMod n) := by push_cast; ring
        have e2 : ((m + 1 : ℕ) : ZMod n) + 1 = ((m + 2 : ℕ) : ZMod n) := by push_cast; ring
        rw [e1, e2, hm, hm1] at hcon
        have : ((m + 1 + 1 : ℕ) : ZMod n) = ((m + 2 : ℕ) : ZMod n) := by push_cast; ring
        rw [this]
        simpa using hcon
  funext i
  show s i = 0
  have : ((i.val : ℕ) : ZMod n) = i := by simp [ZMod.natCast_val, ZMod.cast_id]
  have hk := (key i.val).1
  rwa [this] at hk
