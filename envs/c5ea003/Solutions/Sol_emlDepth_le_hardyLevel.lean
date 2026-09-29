-- Prove2me | solution 1 for emlDepth_le_hardyLevel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:24:39.914121+00:00
-- url     : https://prove2.me/submissions/ed5719ae-d025-4040-aab4-aaed264c9d38

-- Sol generated from EML/HardyEmlBase.lean
import Mathlib
import Definitions.Def_EML_HardyEmlBase
import Theorems.Thm_EmlClass_mono

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






/-- Members of `EmlClass n` have Hardy level `n`. -/
theorem HardyLevel.of_emlClass {n : ℕ} {f : ℝ → ℝ} (h : EmlClass n f) : HardyLevel n f :=
  ⟨f, h, 0, fun _ _ => rfl⟩


/-- Hardy level is monotone in the level. -/
theorem hardyLevel_mono {m n : ℕ} {f : ℝ → ℝ} (hmn : m ≤ n) (hf : HardyLevel m f) :
    HardyLevel n f := by
  obtain ⟨g, hg, X, hX⟩ := hf
  exact ⟨g, hg.mono hmn, X, hX⟩


/-- Hardy levels are closed under sums. -/
theorem hardyLevel_add {n : ℕ} {f g : ℝ → ℝ} (hf : HardyLevel n f) (hg : HardyLevel n g) :
    HardyLevel n (fun x => f x + g x) := by
  obtain ⟨u, hu, X₁, hX₁⟩ := hf
  obtain ⟨v, hv, X₂, hX₂⟩ := hg
  refine ⟨fun x => u x + v x, hu.add hv, max X₁ X₂, fun x hx => ?_⟩
  show u x + v x = f x + g x
  rw [hX₁ x (le_trans (le_max_left _ _) hx), hX₂ x (le_trans (le_max_right _ _) hx)]

/-- Hardy levels are closed under products. -/
theorem hardyLevel_mul {n : ℕ} {f g : ℝ → ℝ} (hf : HardyLevel n f) (hg : HardyLevel n g) :
    HardyLevel n (fun x => f x * g x) := by
  obtain ⟨u, hu, X₁, hX₁⟩ := hf
  obtain ⟨v, hv, X₂, hX₂⟩ := hg
  refine ⟨fun x => u x * v x, hu.mul hv, max X₁ X₂, fun x hx => ?_⟩
  show u x * v x = f x * g x
  rw [hX₁ x (le_trans (le_max_left _ _) hx), hX₂ x (le_trans (le_max_right _ _) hx)]

/-- Hardy levels are closed under negation. -/
theorem hardyLevel_neg {n : ℕ} {f : ℝ → ℝ} (hf : HardyLevel n f) :
    HardyLevel n (fun x => -(f x)) := by
  obtain ⟨u, hu, X, hX⟩ := hf
  exact ⟨fun x => -(u x), hu.neg, X, fun x hx => by show -(u x) = -(f x); rw [hX x hx]⟩

/-- **The exponential shell raises the Hardy level by one.** -/
theorem hardyLevel_closed_under_eml {m n : ℕ} {f g : ℝ → ℝ}
    (hf : HardyLevel m f) (hg : HardyLevel n g) :
    HardyLevel (1 + max m n) (fun x => f x * Real.exp (g x)) := by
  obtain ⟨u, hu, X₁, hX₁⟩ := hf
  obtain ⟨v, hv, X₂, hX₂⟩ := hg
  refine ⟨fun x => u x * Real.exp (v x), hu.shell hv, max X₁ X₂, fun x hx => ?_⟩
  show u x * Real.exp (v x) = f x * Real.exp (g x)
  rw [hX₁ x (le_trans (le_max_left _ _) hx), hX₂ x (le_trans (le_max_right _ _) hx)]


/-! ## The bottom of the hierarchy -/








/-! ## Convenience aliases -/







/-! ## Iterated exponentials -/








theorem solution(e : EmlExpr) : HardyLevel e.emlDepth (fun x => e.eval x) := by
  induction e with
  | var => exact HardyLevel.of_emlClass (EmlClass.id 0)
  | const c => exact HardyLevel.of_emlClass (EmlClass.const 0 c)
  | add a b iha ihb =>
      exact hardyLevel_add (hardyLevel_mono (le_max_left _ _) iha)
        (hardyLevel_mono (le_max_right _ _) ihb)
  | mul a b iha ihb =>
      exact hardyLevel_mul (hardyLevel_mono (le_max_left _ _) iha)
        (hardyLevel_mono (le_max_right _ _) ihb)
  | neg a ih => exact hardyLevel_neg ih
  | eml a b iha ihb => exact hardyLevel_closed_under_eml iha ihb
