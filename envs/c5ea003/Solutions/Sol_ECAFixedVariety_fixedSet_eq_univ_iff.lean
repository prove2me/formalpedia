-- Prove2me | solution 1 for ECAFixedVariety.fixedSet_eq_univ_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:54:37.007394+00:00
-- url     : https://prove2.me/submissions/7b3ffd87-72fa-412d-b8ec-5b5332499833

-- Sol generated from Novelty/ECAMaximalDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAPeriodicPointLattice
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff

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

/-- On a ring of size at least `3` the cells `0, 1, 2` are distinct. -/
lemma zmod_zero_one_two_distinct {n : ℕ} (hn : 3 ≤ n) :
    (0 : ZMod n) ≠ 1 ∧ (1 : ZMod n) ≠ 2 ∧ (0 : ZMod n) ≠ 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have e1 : ((1 : ℕ) : ZMod n) = 1 := by push_cast; ring
  have e2 : ((2 : ℕ) : ZMod n) = 2 := by push_cast; ring
  have v0 : (0 : ZMod n).val = 0 := ZMod.val_zero
  have v1 : (1 : ZMod n).val = 1 := by rw [← e1, ZMod.val_natCast_of_lt (by omega)]
  have v2 : (2 : ZMod n).val = 2 := by rw [← e2, ZMod.val_natCast_of_lt (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> [rw [h] at v0; rw [h] at v1; rw [h] at v0] <;> omega

/-- **Independence of the local windows.**  For `n ≥ 3` every prescribed
neighbourhood `(l, c, r)` occurs as the window around the cell `1`. -/
theorem exists_cfg_window {n : ℕ} (hn : 3 ≤ n) (l c r : ZMod 2) :
    ∃ s : Cfg n, s (1 - 1) = l ∧ s 1 = c ∧ s (1 + 1) = r := by
  obtain ⟨h01, h12, h02⟩ := zmod_zero_one_two_distinct hn
  refine ⟨fun i => if i = 0 then l else if i = 1 then c else if i = 2 then r else 0, ?_, ?_, ?_⟩
  · simp
  · simp [h01.symm]
  · have e : (1 : ZMod n) + 1 = 2 := by ring
    rw [e]
    simp [h02.symm, h12.symm]







open ECAFixedVariety in
theorem solution{rule n : ℕ} (hn : 3 ≤ n) :
    fixedSet rule n = Set.univ ↔ ∀ l c r : ZMod 2, localRuleZ rule l c r = c := by
  constructor
  · intro h l c r
    obtain ⟨s, hl, hc, hr⟩ := exists_cfg_window (n := n) hn l c r
    have hs : s ∈ fixedSet rule n := by rw [h]; trivial
    rw [mem_fixedSet_iff] at hs
    have := hs 1
    rwa [hl, hc, hr] at this
  · intro h
    ext s
    simp only [Set.mem_univ, iff_true, mem_fixedSet_iff]
    intro i
    exact h _ _ _
