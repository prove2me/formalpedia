-- Prove2me | solution 1 for ECAFixedVariety.rule30_fixedSet_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:49.566954+00:00
-- url     : https://prove2.me/submissions/f70a744d-8b9e-4fd3-92d9-2ffc71747522

-- Sol generated from Novelty/ECARule30Chaos.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAParityRule150
import Definitions.Def_Novelty_ECASymmetryOrbit
import Theorems.Thm_ECAFixedVariety_constant_of_shift_one
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff
import Theorems.Thm_ECAFixedVariety_shift_one_of_period_coprime

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













open ECAFixedVariety in
theorem solution{n : ℕ} (hn : ¬ (2 ∣ n)) : fixedSet 30 n = {0} := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, rfl⟩
  haveI : NeZero n := ⟨hn0⟩
  have hcop : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hn
  ext s
  rw [Set.mem_singleton_iff]
  constructor
  · intro hs
    have hper : ∀ i, s (i + ((2 : ℕ) : ZMod n)) = s i := by
      intro i
      simpa using rule30_period_two hs i
    have hconst := constant_of_shift_one (shift_one_of_period_coprime hn0 hcop hper)
    have hfix := (mem_fixedSet_iff.1 hs) 0
    rw [hconst (0 - 1), hconst (0 + 1)] at hfix
    have hzero : s 0 = 0 := (rule30_const_iff (s 0)).1 hfix
    funext i
    show s i = 0
    rw [hconst i, hzero]
  · rintro rfl
    exact rule30_zero_mem
