-- Prove2me | solution 1 for ECAFixedVariety.rule30_fixedSet_of_even
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:48.974859+00:00
-- url     : https://prove2.me/submissions/8a225e29-04b1-4b91-ad47-2ed9e886b3ff

-- Sol generated from Novelty/ECARule30Chaos.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAParityRule150
import Definitions.Def_Novelty_ECASymmetryOrbit
import Theorems.Thm_ECAFixedVariety_eq_of_period_two_seed
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff
import Theorems.Thm_ECAFixedVariety_rule30_conj_alternating_mem
import Theorems.Thm_ECAFixedVariety_zmod2_eq_zero_or_one

/-!
# Cycle 6: Rule 30, the canonical chaotic automaton, has a three-point locus

Rule 30 is Wolfram's flagship class-3 rule (it was used as a random number
generator).  Its stationarity constraints are

* `s_i = 0 ⟹ s_{i-1} = s_{i+1}`, and
* `s_i = 1 ⟹ s_{i-1} = 0`,

which force spatial period two.  We determine its fixed-point locus completely:

* `rule30_period_two` — every stationary configuration has period `2`.
* `rule30_fixedSet_of_odd` — on an odd ring only the zero configuration is
  stationary.
* `rule30_fixedSet_of_even` — on an even ring the locus is exactly
  `{0, alternating, ¬alternating}`, a **three**-point set.
* `rule30_ncard_of_even`, `rule30_not_affine_of_even`,
  `rule30_no_fixed_dim_of_even` — since `3 ∤ 2ⁿ`, the locus of the canonical
  chaotic rule is not an affine subvariety and has **no dimension**, for
  infinitely many ring sizes at once (not merely in a single computed example).

This upgrades the Lagrange obstruction of Cycle 1 from a finite check to an
infinite family, and it does so for the very rule that the conjecture would
place at `dim ≥ n/2`.
-/

open ECAFixedVariety

/-- Stationarity relation of Rule 30, in transfer form. -/
lemma rule30_transfer :
    ∀ a b c d : ZMod 2, localRuleZ 30 a b c = b → localRuleZ 30 b c d = c → c = a := by decide

/-- Only the zero cell value is stationary in a constant environment. -/
lemma rule30_const_iff : ∀ x : ZMod 2, localRuleZ 30 x x x = x ↔ x = 0 := by decide

/-- **Transfer relation for Rule 30.**  Stationary configurations have spatial
period two. -/
theorem rule30_period_two {n : ℕ} {s : Cfg n} (hs : s ∈ fixedSet 30 n) :
    ∀ i, s (i + 2) = s i := by
  rw [mem_fixedSet_iff] at hs
  intro i
  have h1 := hs (i + 1)
  have h2 := hs (i + 2)
  rw [show i + 1 - 1 = i from by ring, show i + 1 + 1 = i + 2 from by ring] at h1
  rw [show i + 2 - 1 = i + 1 from by ring, show i + 2 + 1 = i + 3 from by ring] at h2
  exact rule30_transfer _ _ _ _ h1 h2

/-- The zero configuration is stationary for Rule 30. -/
lemma rule30_zero_mem {n : ℕ} : (0 : Cfg n) ∈ fixedSet 30 n := by
  rw [mem_fixedSet_iff]
  intro i
  simpa using (rule30_const_iff 0).2 rfl


/-! ### Even rings: an explicit three-point locus -/

/-- The alternating configuration has spatial period two. -/
lemma alternating_period_two {n : ℕ} (h : 2 ∣ n) :
    ∀ i, alternating h (i + 2) = alternating h i := by
  intro i
  show ZMod.castHom h (ZMod 2) (i + 2) = ZMod.castHom h (ZMod 2) i
  rw [map_add]
  have h2 : ZMod.castHom h (ZMod 2) 2 = 0 := by
    have : (2 : ZMod n) = ((2 : ℕ) : ZMod n) := by push_cast; ring
    rw [this, map_natCast]
    decide
  rw [h2, add_zero]

lemma conjCfg_period_two {n : ℕ} {s : Cfg n} (h : ∀ i, s (i + 2) = s i) :
    ∀ i, conjCfg s (i + 2) = conjCfg s i := by
  intro i
  show 1 + s (i + 2) = 1 + s i
  rw [h]

@[simp] lemma alternating_zero {n : ℕ} (h : 2 ∣ n) : alternating h 0 = 0 := by
  show ZMod.castHom h (ZMod 2) 0 = 0
  rw [map_zero]

@[simp] lemma alternating_one {n : ℕ} (h : 2 ∣ n) : alternating h 1 = 1 := by
  show ZMod.castHom h (ZMod 2) 1 = 1
  rw [map_one]

/-- The alternating configuration is stationary for Rule 30. -/
theorem rule30_alternating_mem {n : ℕ} (h : 2 ∣ n) : alternating h ∈ fixedSet 30 n := by
  rw [mem_fixedSet_iff]
  intro i
  have e1 : ZMod.castHom h (ZMod 2) (i - 1) = ZMod.castHom h (ZMod 2) i - 1 := by
    rw [map_sub, map_one]
  have e2 : ZMod.castHom h (ZMod 2) (i + 1) = ZMod.castHom h (ZMod 2) i + 1 := by
    rw [map_add, map_one]
  have key : ∀ x : ZMod 2, localRuleZ 30 (x - 1) x (x + 1) = x := by decide
  simp only [alternating, e1, e2]
  exact key _








open ECAFixedVariety in
theorem solution{n : ℕ} (h : 2 ∣ n) (hn : n ≠ 0) :
    fixedSet 30 n = {0, alternating h, conjCfg (alternating h)} := by
  haveI : NeZero n := ⟨hn⟩
  have halt := alternating_period_two h
  have hconj := conjCfg_period_two halt
  have hzero : ∀ i : ZMod n, (0 : Cfg n) (i + 2) = (0 : Cfg n) i := fun _ => rfl
  have hone : ∀ i : ZMod n, (1 : Cfg n) (i + 2) = (1 : Cfg n) i := fun _ => rfl
  ext s
  constructor
  · intro hs
    have hper := rule30_period_two hs
    rcases zmod2_eq_zero_or_one (s 0) with h0 | h0 <;>
      rcases zmod2_eq_zero_or_one (s 1) with h1 | h1
    · left
      exact eq_of_period_two_seed hper hzero (by simpa using h0) (by simpa using h1)
    · right; left
      exact eq_of_period_two_seed hper halt (by simp [h0]) (by simp [h1])
    · right; right
      refine eq_of_period_two_seed hper hconj ?_ ?_
      · rw [show (conjCfg (alternating h)) 0 = 1 + alternating h 0 from rfl, h0,
          alternating_zero]
        decide
      · rw [show (conjCfg (alternating h)) 1 = 1 + alternating h 1 from rfl, h1,
          alternating_one]
        decide
    · -- the all-ones configuration is not stationary for Rule 30
      exfalso
      have hall : s = 1 :=
        eq_of_period_two_seed hper hone (by simpa using h0) (by simpa using h1)
      have hfix := (mem_fixedSet_iff.1 hs) 0
      rw [hall] at hfix
      have : localRuleZ 30 1 1 1 = 1 := hfix
      have hcontr := (rule30_const_iff 1).1 this
      exact absurd hcontr (by decide)
  · rintro (rfl | rfl | rfl)
    · exact rule30_zero_mem
    · exact rule30_alternating_mem h
    · exact rule30_conj_alternating_mem h
