-- Prove2me | Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
-- name    : Couret_RecohRationalComplex_e4146c64164f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:08.816739+00:00
-- url     : https://prove2.me/theorems/46146da0-52cd-41d1-b093-4c15586fd011
-- title:
--   Rational complex coordinates and squared distance
-- statement:
--   Uses a pair of rationals as executable complex coordinates. recohRationalComplexValue embeds the two coordinates as the real and imaginary parts of a complex number. recohRationalSquaredDistance computes the rational sum of the squares of coordinate differences, with no square root or complex comparison.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalComplex.lean; source file SHA-256 c7ad43f0d63569d28a37773ed02641e34239f2ed0c451642062ac97af4d5d57c

import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Executable rational complex coordinates and their exact norm semantics. -/

namespace Couret.STROBO2TORS

/-- Executable rational complex coordinates. -/
abbrev RecohRationalComplex := ℚ × ℚ

noncomputable def recohRationalComplexValue (z : RecohRationalComplex) : ℂ :=
  ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

def recohRationalSquaredDistance (z w : RecohRationalComplex) : ℚ :=
  (z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2





end Couret.STROBO2TORS


