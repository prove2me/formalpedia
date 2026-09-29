-- Prove2me | solution 1 for Bishop.Reg.approx_locate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:26:44.891034+00:00
-- url     : https://prove2.me/submissions/b061e830-3ad0-40a1-8a30-531651ffe2bb

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveOrder.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
import Theorems.Thm_Bishop_Reg_approx_locate_left
import Theorems.Thm_Bishop_Reg_approx_locate_right
/-
# The constructive order on Bishop reals

Constructively, the order relation on the reals is *not* obtained by negating an
equality: `x < y` must carry positive information.  Bishop defines, for regular
sequences of rationals,

  `x > 0`  iff  `∃ n, x n > 1/n`,      `x < y`  iff  `y - x > 0`,

so that a proof of `x < y` is a *witness index* together with a rational
inequality, from which a rational lower bound on the gap `y - x` can be read off.

This file develops that order for the Bishop reals of
`Logic/ConstructiveAnalysis/BishopReals.lean`:

* `Bishop.Reg.pos_iff_toReal_pos`, `Bishop.Reg.lt_iff_toReal_lt` : the witnessed
  relations agree with the classical order on the denoted reals (so nothing is
  lost, and the constructive relation is not weaker);
* `Bishop.Reg.lt_cotrans` : **cotransitivity**, the constructive substitute for
  trichotomy, in fully explicit form — from a witness `n` for `x < y` one computes
  an index `m` at which a *decidable rational comparison* of `z.approx m` with the
  midpoint `(x.approx m + y.approx m)/2` decides between `x < z` and `z < y`;
* `Bishop.Reg.approx_locate_left`, `approx_locate_right`, `approx_locate` : the
  constructive location lemma — for rationals `a < b`, a single rational
  comparison at a computed index decides `a < x` or `x < b`;
* `Bishop.Reg.no_uniform_lt_witness` : the witness index in `x < y` cannot be
  bounded in advance — the precise sense in which the order, though it agrees
  extensionally with the classical one, is not decidable at bounded precision.
-/


open Bishop

open Reg

/-! ## Two-sided form of the explicit modulus -/



/-- An index at which the canonical accuracy `C/(n+1)` beats a given positive real. -/
lemma exists_nat_inv_lt (C : ℝ) {t : ℝ} (ht : 0 < t) : ∃ n : ℕ, C / (n + 1) < t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / t)
  refine ⟨n, ?_⟩
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ h1]
  have h2 : C / t < (n : ℝ) + 1 := by linarith
  have h3 : C / t * t < ((n : ℝ) + 1) * t := by
    exact mul_lt_mul_of_pos_right h2 ht
  have h4 : C / t * t = C := by field_simp
  linarith [h3, h4]

/-! ## Positivity and the strict order -/














/-! ## Locating a Bishop real between two rationals -/




/-! ## The order is not decidable at bounded precision -/




open Bishop.Reg in
theorem solution(x : Reg) {a b : ℚ} (hab : a < b) :
    (a : ℝ) < x.toReal ∨ x.toReal < (b : ℝ) := by
  have habR : (0 : ℝ) < ((b - a : ℚ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  obtain ⟨n, hnR⟩ := exists_nat_inv_lt 4 habR
  have hn : 4 / (n + 1 : ℚ) ≤ b - a := by
    have : ((4 / (n + 1 : ℚ) : ℚ) : ℝ) ≤ ((b - a : ℚ) : ℝ) := by
      push_cast
      push_cast at hnR
      linarith
    exact_mod_cast this
  by_cases h : (a + b) / 2 ≤ x.approx n
  · exact Or.inl (approx_locate_left hn h)
  · push_neg at h
    exact Or.inr (approx_locate_right hn h)
