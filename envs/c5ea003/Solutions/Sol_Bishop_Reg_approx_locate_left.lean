-- Prove2me | solution 1 for Bishop.Reg.approx_locate_left
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:35:29.782128+00:00
-- url     : https://prove2.me/submissions/c1fe8070-7138-4256-a4a5-7d485f4cc1f6

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveOrder.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
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

lemma toReal_lower (x : Reg) (n : ℕ) : (x.approx n : ℝ) - 1 / (n + 1) ≤ x.toReal := by
  have h := abs_le.mp (x.abs_toReal_sub_approx_le n)
  linarith [h.1]



/-! ## Positivity and the strict order -/














/-! ## Locating a Bishop real between two rationals -/




/-! ## The order is not decidable at bounded precision -/




namespace Bishop.Reg
lemma toReal_lower (x : Reg) (n : ℕ) : (x.approx n : ℝ) - 1 / (n + 1) ≤ x.toReal := by
  have h := abs_le.mp (x.abs_toReal_sub_approx_le n)
  linarith [h.1]

end Bishop.Reg

open Bishop in
theorem solution{x : Reg} {a b : ℚ} {n : ℕ}
    (hn : 4 / (n + 1 : ℚ) ≤ b - a) (h : (a + b) / 2 ≤ x.approx n) :
    (a : ℝ) < x.toReal := by
  have hnR : (4 : ℝ) / ((n : ℝ) + 1) ≤ (b : ℝ) - (a : ℝ) := by
    have : ((4 / (n + 1 : ℚ) : ℚ) : ℝ) ≤ ((b - a : ℚ) : ℝ) := by exact_mod_cast hn
    push_cast at this
    exact this
  have hR : ((a : ℝ) + (b : ℝ)) / 2 ≤ (x.approx n : ℝ) := by
    have : (((a + b) / 2 : ℚ) : ℝ) ≤ ((x.approx n : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at this
    exact this
  have hlow := x.toReal_lower n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h4 : (1 : ℝ) / ((n : ℝ) + 1) ≤ ((b : ℝ) - (a : ℝ)) / 4 := by
    have he : (4 : ℝ) / ((n : ℝ) + 1) = 4 * (1 / ((n : ℝ) + 1)) := by ring
    rw [he] at hnR
    linarith
  have hab : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
    have : (0 : ℝ) < 4 / ((n : ℝ) + 1) := by positivity
    linarith
  linarith
