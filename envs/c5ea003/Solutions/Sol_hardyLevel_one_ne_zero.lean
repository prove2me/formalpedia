-- Prove2me | solution 1 for hardyLevel_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:24:54.996989+00:00
-- url     : https://prove2.me/submissions/1a3ad6ad-883f-499d-9251-8cf6cba7eb14

-- Sol generated from EML/HardyEmlBase.lean
import Mathlib
import Definitions.Def_EML_HardyEmlBase
import Theorems.Thm_EmlClass_eq_polynomial_of_level_zero

/-!
# EML expressions, their depth, and the Hardy level hierarchy

This file provides the common vocabulary for the exponential–logarithmic (EML)
depth theory used elsewhere in the catalog.

## Contents

* `EmlExpr` — the full EML expression grammar: the variable, real constants,
  `+`, `*`, negation, and the *exponential shell* `eml a b = a · exp b`.
  Its semantics is `EmlExpr.eval` and its exponential nesting depth is
  `EmlExpr.emlDepth`.
* `EmlClass n f` — the inductively defined class of real functions built from
  constants and the identity by `+`, `*`, `-` and at most `n` nested
  exponentials.
* `HardyLevel n f` — `f` agrees with a member of `EmlClass n` near `+∞`.  This
  is the semantic ("Hardy level") counterpart of `emlDepth` and is stable under
  eventual equality (`HardyLevel.congr`) and monotone in the level
  (`hardyLevel_mono`).
* `emlDepth_le_hardyLevel` — the bridge: an expression of EML depth `d`
  evaluates to a function of Hardy level `d`.
* `hardyLevel_closed_under_eml` — the exponential shell raises the level by one.
* `hardyLevel_zero_eq_polynomial` and `hardyLevel_one_ne_zero` — the hierarchy
  starts strictly: level `0` consists exactly of the eventually-polynomial
  functions, and `Real.exp`, which sits at level `1`, is not of level `0`.
-/

noncomputable section

open Real

/-! ## The full EML expression grammar -/


open EmlExpr




/-! ## The semantic hierarchy -/



open EventuallyEq'















/-! ## The bottom of the hierarchy -/


/-- Every member of `EmlClass 0` is a polynomial function. -/
theorem EmlClass.zero_eq_polynomial {f : ℝ → ℝ} (h : EmlClass 0 f) :
    ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x :=
  h.eq_polynomial_of_level_zero rfl

/-- Powers of the variable belong to `EmlClass 0`. -/
theorem EmlClass.pow (k : ℕ) : EmlClass 0 (fun x : ℝ => x ^ k) := by
  induction k with
  | zero => simpa using EmlClass.const 0 1
  | succ k ih => simpa [pow_succ] using ih.mul (EmlClass.id 0)

/-- Every polynomial function belongs to `EmlClass 0`. -/
theorem EmlClass.of_polynomial (p : Polynomial ℝ) : EmlClass 0 (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
      simpa [Polynomial.eval_monomial] using (EmlClass.const 0 a).mul (EmlClass.pow n)

/-- **Level `0` is exactly the eventually-polynomial functions.** -/
theorem hardyLevel_zero_eq_polynomial {f : ℝ → ℝ} :
    HardyLevel 0 f ↔ ∃ (p : Polynomial ℝ) (X : ℝ), ∀ x ≥ X, p.eval x = f x := by
  constructor
  · rintro ⟨g, hg, X, hX⟩
    obtain ⟨p, hp⟩ := hg.zero_eq_polynomial
    exact ⟨p, X, fun x hx => by rw [← hp x]; exact hX x hx⟩
  · rintro ⟨p, X, hX⟩
    exact ⟨fun x => p.eval x, EmlClass.of_polynomial p, X, hX⟩



/-! ## Convenience aliases -/







/-! ## Iterated exponentials -/








theorem solution: ¬ HardyLevel 0 Real.exp := by
  rw [hardyLevel_zero_eq_polynomial]
  rintro ⟨p, X, hX⟩
  -- `p.eval x / exp x → 0`, yet it is eventually equal to `1`
  have h0 : Filter.Tendsto (fun x : ℝ => p.eval x / Real.exp x) Filter.atTop (nhds 0) :=
    p.tendsto_div_exp_atTop
  have h1 : Filter.Tendsto (fun x : ℝ => p.eval x / Real.exp x) Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop X] with x hx
    rw [hX x hx, div_self (Real.exp_ne_zero x)]
  have := tendsto_nhds_unique h0 h1
  norm_num at this
