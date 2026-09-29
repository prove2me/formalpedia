-- Prove2me | Theorems.Thm_EmlClass_mono
-- name    : EmlClass.mono
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:22:39.59217+00:00
-- url     : https://prove2.me/theorems/5e1390ec-5329-4322-be60-520c91d0598c
-- title:
--   `EmlClass` is monotone in the level.
-- statement:
--   `EmlClass` is monotone in the level.
--
--   ```lean
--   theorem EmlClass.mono: ∀ {m n : ℕ} {f : ℝ → ℝ}, m ≤ n → EmlClass m f → EmlClass n f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `EML/HardyEmlBase.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/EML/HardyEmlBase.lean#L114

-- Thm stub generated from EML/HardyEmlBase.lean
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

theorem EmlClass.mono: ∀ {m n : ℕ} {f : ℝ → ℝ}, m ≤ n → EmlClass m f → EmlClass n f := by sorry
