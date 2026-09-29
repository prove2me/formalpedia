-- Prove2me | solution 1 for Bishop.Reg.lt_cotrans_or
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:27:48.089085+00:00
-- url     : https://prove2.me/submissions/981b5d9f-e6c1-4712-b501-df6fc4c0c55f

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveOrder.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
import Theorems.Thm_Bishop_Reg_gap_le_approx_sub
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









lemma gapAt_pos {x y : Reg} {n : ℕ} (h : x.approx n + 2 / (n + 1 : ℚ) < y.approx n) :
    0 < gapAt x y n := by
  simp only [gapAt]
  linarith



/-- **Cotransitivity of the constructive order (explicit form).**

From a witness `n` for `x < y` one computes an index `m` (any index with
`1/(m+1) ≤ gapAt x y n / 8`) at which, for *any* third Bishop real `z`, a single
decidable comparison of the rationals `z.approx m` and `(x.approx m + y.approx m)/2`
decides between `x < z` and `z < y`.  This is the constructive substitute for the
classically trivial disjunction `x < z ∨ z < y`. -/
theorem lt_cotrans {x y : Reg} {n : ℕ}
    (h : x.approx n + 2 / (n + 1 : ℚ) < y.approx n) (z : Reg) {m : ℕ}
    (hm : 1 / (m + 1 : ℚ) ≤ gapAt x y n / 8) :
    (x.approx m + 2 / (m + 1 : ℚ) < z.approx m ∨
      z.approx m + 2 / (m + 1 : ℚ) < y.approx m) := by
  have hg : 0 < gapAt x y n := gapAt_pos h
  have hspread := gap_le_approx_sub x y n hm
  have hstep : (2 : ℚ) / (m + 1) ≤ gapAt x y n / 4 := by
    have he : (2 : ℚ) / ((m : ℚ) + 1) = 2 * (1 / ((m : ℚ) + 1)) := by ring
    rw [he]
    linarith
  by_cases hz : (x.approx m + y.approx m) / 2 ≤ z.approx m
  · left; linarith
  · push_neg at hz
    right; linarith


/-! ## Locating a Bishop real between two rationals -/




/-! ## The order is not decidable at bounded precision -/




open Bishop.Reg in
theorem solution{x y : Reg} (h : Lt x y) (z : Reg) : Lt x z ∨ Lt z y := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hmR⟩ :=
    exists_nat_inv_lt 1 (t := ((gapAt x y n : ℚ) : ℝ) / 8)
      (by
        have := gapAt_pos hn
        have : (0 : ℝ) < ((gapAt x y n : ℚ) : ℝ) := by exact_mod_cast this
        linarith)
  have hm : 1 / (m + 1 : ℚ) ≤ gapAt x y n / 8 := by
    have : ((1 / (m + 1 : ℚ) : ℚ) : ℝ) ≤ ((gapAt x y n / 8 : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  rcases lt_cotrans hn z hm with hc | hc
  · exact Or.inl ⟨m, hc⟩
  · exact Or.inr ⟨m, hc⟩
