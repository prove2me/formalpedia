-- Prove2me | Definitions.Def_EML_HardyEmlBase
-- name    : EML_HardyEmlBase
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:31.905315+00:00
-- url     : https://prove2.me/theorems/00db3c36-937a-47ba-8f47-bf0457f246ae
-- title:
--   Aether Catalog definitions — EML_HardyEmlBase
-- statement:
--   Definition bundle for the Aether Catalog module `EML.HardyEmlBase`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/HardyEmlBase.lean by skeleton subtraction
import Mathlib

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

/-- Syntax of full EML expressions in one real variable.  The constructor
`eml a b` denotes the *exponential shell* `a · exp b`; ordinary exponentials are
the special case `eml 1 b`. -/
inductive EmlExpr : Type where
  | var : EmlExpr
  | const : ℝ → EmlExpr
  | add : EmlExpr → EmlExpr → EmlExpr
  | mul : EmlExpr → EmlExpr → EmlExpr
  | neg : EmlExpr → EmlExpr
  | eml : EmlExpr → EmlExpr → EmlExpr
  deriving Inhabited

namespace EmlExpr

/-- Interpretation of an EML expression as a real function. -/
def eval : EmlExpr → ℝ → ℝ
  | var, x => x
  | const c, _ => c
  | add a b, x => a.eval x + b.eval x
  | mul a b, x => a.eval x * b.eval x
  | neg a, x => -(a.eval x)
  | eml a b, x => a.eval x * Real.exp (b.eval x)

/-- The exponential nesting depth of an EML expression: only the exponential
shells `eml` contribute. -/
def emlDepth : EmlExpr → ℕ
  | var => 0
  | const _ => 0
  | add a b => max a.emlDepth b.emlDepth
  | mul a b => max a.emlDepth b.emlDepth
  | neg a => a.emlDepth
  | eml a b => 1 + max a.emlDepth b.emlDepth

end EmlExpr

/-! ## The semantic hierarchy -/

/-- `EmlClass n f` : the function `f` is built from real constants and the
identity using `+`, `*`, `-` and at most `n` nested exponentials. -/
inductive EmlClass : ℕ → (ℝ → ℝ) → Prop where
  | const (n : ℕ) (c : ℝ) : EmlClass n (fun _ => c)
  | id (n : ℕ) : EmlClass n (fun x => x)
  | add {n : ℕ} {f g : ℝ → ℝ} : EmlClass n f → EmlClass n g → EmlClass n (fun x => f x + g x)
  | mul {n : ℕ} {f g : ℝ → ℝ} : EmlClass n f → EmlClass n g → EmlClass n (fun x => f x * g x)
  | neg {n : ℕ} {f : ℝ → ℝ} : EmlClass n f → EmlClass n (fun x => -(f x))
  | shell {m n : ℕ} {f g : ℝ → ℝ} :
      EmlClass m f → EmlClass n g →
      EmlClass (1 + max m n) (fun x => f x * Real.exp (g x))

/-- Two functions are **eventually equal** if they agree on some half-line
`[X, ∞)`.  Hardy levels only see this equivalence relation. -/
def EventuallyEq' (f g : ℝ → ℝ) : Prop := ∃ X : ℝ, ∀ x ≥ X, f x = g x

namespace EventuallyEq'




end EventuallyEq'

/-- `HardyLevel n f` : the function `f` coincides, near `+∞`, with a function of
`EmlClass n`.  This is the Hardy-hierarchy level of `f`. -/
def HardyLevel (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, EmlClass n g ∧ EventuallyEq' g f










/-! ## The bottom of the hierarchy -/








/-! ## Convenience aliases -/







/-! ## Iterated exponentials -/

/-- The `n`-fold iterated exponential `exp (exp (⋯ (x)))`, the canonical
inhabitant of Hardy level `n`. -/
def iterExp : ℕ → (ℝ → ℝ)
  | 0 => id
  | n + 1 => fun x => Real.exp (iterExp n x)






end


