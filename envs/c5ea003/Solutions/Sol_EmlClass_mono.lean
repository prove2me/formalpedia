-- Prove2me | solution 1 for EmlClass.mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:23:08.135684+00:00
-- url     : https://prove2.me/submissions/9f1cf237-0dde-4e4f-ad76-fe3dc38ddb62

-- Sol generated from EML/HardyEmlBase.lean
import Mathlib
import Definitions.Def_EML_HardyEmlBase

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








/-! ## Convenience aliases -/







/-! ## Iterated exponentials -/








theorem solution: ∀ {m n : ℕ} {f : ℝ → ℝ}, m ≤ n → EmlClass m f → EmlClass n f := by
  intro m n f hmn hf
  induction hf generalizing n with
  | const _ c => exact EmlClass.const _ c
  | id _ => exact EmlClass.id _
  | add _ _ iha ihb => exact (iha hmn).add (ihb hmn)
  | mul _ _ iha ihb => exact (iha hmn).mul (ihb hmn)
  | neg _ ih => exact (ih hmn).neg
  | @shell m₁ m₂ f g hf hg ihf ihg =>
      obtain ⟨k, rfl⟩ : ∃ k, n = 1 + max m₁ m₂ + k := ⟨n - (1 + max m₁ m₂), by omega⟩
      have h1 : m₁ ≤ max m₁ m₂ + k := le_trans (le_max_left _ _) (Nat.le_add_right _ _)
      have h2 : m₂ ≤ max m₁ m₂ + k := le_trans (le_max_right _ _) (Nat.le_add_right _ _)
      have := (ihf h1).shell (ihg h2)
      simpa [Nat.max_self, Nat.add_assoc] using this
