-- Prove2me | Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
-- name    : Couret_RecohTripleNewton_821bcf694d07
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:35.977465+00:00
-- url     : https://prove2.me/theorems/a819a7da-ed75-45ac-ab3d-eb041cdeb67b
-- title:
--   Rational choice between a character and its cube
-- statement:
--   For m : ℚ, recohNewtonMultiplier m is one when 3/8 ≤ m and three otherwise; equality at the threshold chooses one. For arbitrary complex z₁,z₂,z₃, recohNewtonSelectedProbe is the sum of each z value raised to this selected exponent. It is the sum of the powered values, not the power of their sum. The definitions assume neither unit norms nor distinctness of the z values and do not supply an approximation certificate or a lower bound on the selected probe.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohTripleNewton.lean; source file SHA-256 c0dfe04ad32a6cb240d859da6d7a72431007a71855a11b54c052d91aa4f8724e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Quantitative Newton identity for three unit complex numbers, and the
two-choice rational protocol used to replace a character by itself or its
cube before any support reading is measured.

The cube reading is the sum of the cubes of the three values. It is not the
cube of their sum. No distinctness of the values is assumed.

The rational comparison below is executable. Its correctness theorem takes
an explicit approximation certificate; this module does not construct that
certificate or establish extensionality for arbitrary approximation routines.
-/

namespace Couret.STROBO2TORS













/-- Executable rational threshold: retain the character or take its cube. -/
def recohNewtonMultiplier (m : ℚ) : ℕ :=
  if (3 / 8 : ℚ) ≤ m then 1 else 3









/-- The semantic selected support reading is a sum of powered values. -/
noncomputable def recohNewtonSelectedProbe (z₁ z₂ z₃ : ℂ) (m : ℚ) : ℂ :=
  z₁ ^ recohNewtonMultiplier m + z₂ ^ recohNewtonMultiplier m + z₃ ^ recohNewtonMultiplier m









end Couret.STROBO2TORS


