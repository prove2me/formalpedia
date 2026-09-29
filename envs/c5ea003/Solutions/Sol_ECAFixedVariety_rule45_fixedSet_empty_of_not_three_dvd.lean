-- Prove2me | solution 1 for ECAFixedVariety.rule45_fixedSet_empty_of_not_three_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:46.34151+00:00
-- url     : https://prove2.me/submissions/bd61cfe7-188b-409a-b087-14818c3ee735

-- Sol generated from Novelty/ECAFixedVarietyPeriodThree.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff
import Theorems.Thm_ECAFixedVariety_rule45_period_three
import Theorems.Thm_ECAFixedVariety_shift_one_of_period_coprime

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

/-- If `3` is invertible modulo `n`, shift-by-three invariance upgrades to
shift-by-one invariance: the configuration is constant. -/
lemma shift_one_of_period_three {n : ℕ} (hn : ¬ (3 ∣ n)) {s : Cfg n}
    (h : ∀ i, s (i + 3) = s i) : ∀ i, s (i + 1) = s i := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, rfl⟩
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hn
  refine shift_one_of_period_coprime hn0 hcop ?_
  intro i
  have hi := h i
  simpa using hi

/-! ### Rule 90 -/










/-! ### Rule 45 -/







open ECAFixedVariety in
theorem solution{n : ℕ} (hn : ¬ (3 ∣ n)) :
    fixedSet 45 n = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  have hshift := shift_one_of_period_three hn (rule45_period_three hs)
  rw [mem_fixedSet_iff] at hs
  have hprev : s 0 = s (0 - 1) := by
    have := hshift (0 - 1)
    rwa [show (0 : ZMod n) - 1 + 1 = 0 from by ring] at this
  have hnext : s (0 + 1) = s 0 := hshift 0
  have h := hs 0
  rw [hnext, ← hprev] at h
  have : ∀ x : ZMod 2, localRuleZ 45 x x x ≠ x := by decide
  exact this _ h
