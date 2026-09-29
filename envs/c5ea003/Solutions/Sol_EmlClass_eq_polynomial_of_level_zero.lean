-- Prove2me | solution 1 for EmlClass.eq_polynomial_of_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:23:07.623428+00:00
-- url     : https://prove2.me/submissions/abf6a8fc-36d1-41dc-b037-8389f6baa3b5

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








theorem solution{n : ℕ} {f : ℝ → ℝ} (h : EmlClass n f) (hn : n = 0) :
    ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x := by
  induction h with
  | const _ c => exact ⟨Polynomial.C c, fun x => by simp⟩
  | id _ => exact ⟨Polynomial.X, fun x => by simp⟩
  | add _ _ iha ihb =>
      obtain ⟨p, hp⟩ := iha hn; obtain ⟨q, hq⟩ := ihb hn
      exact ⟨p + q, fun x => by simp [hp, hq]⟩
  | mul _ _ iha ihb =>
      obtain ⟨p, hp⟩ := iha hn; obtain ⟨q, hq⟩ := ihb hn
      exact ⟨p * q, fun x => by simp [hp, hq]⟩
  | neg _ ih =>
      obtain ⟨p, hp⟩ := ih hn
      exact ⟨-p, fun x => by simp [hp]⟩
  | @shell m k f g _ _ _ _ => omega
