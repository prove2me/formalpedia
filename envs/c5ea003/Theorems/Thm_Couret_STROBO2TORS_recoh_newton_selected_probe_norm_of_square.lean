-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_newton_selected_probe_norm_of_square
-- name    : Couret.STROBO2TORS.recoh_newton_selected_probe_norm_of_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:31.636473+00:00
-- url     : https://prove2.me/theorems/9ded9790-e71d-42bd-ab0e-69d3cbc99405
-- title:
--   A certified squared observation gives a safe Newton probe
-- statement:
--   Let $z_1,z_2,z_3\in\mathbb C$ have modulus one, put $s=z_1+z_2+z_3$, $t=z_1^3+z_2^3+z_3^3$, and $p=z_1z_2z_3$. For $m\in\mathbb Q$, define $\mu(m)=1$ when $m\ge3/8$ and $\mu(m)=3$ otherwise. Let $A\in\mathbb C$ satisfy $A=s^2$ and $|m-|A||\le1/8$. Then
--
--   $$|z_1^{\mu(m)}+z_2^{\mu(m)}+z_3^{\mu(m)}|\ge1/2.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohTripleNewton.lean#L189-L197, lines 189–197; source file SHA-256 c0dfe04ad32a6cb240d859da6d7a72431007a71855a11b54c052d91aa4f8724e; theorem Couret.STROBO2TORS.recoh_newton_selected_probe_norm_of_square

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_newton_selected_probe_norm
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

theorem recoh_newton_selected_probe_norm_of_square (z₁ z₂ z₃ A : ℂ) (m : ℚ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (hA : A = (z₁ + z₂ + z₃) ^ 2)
    (hcert : |(m : ℝ) - ‖A‖| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ ‖recohNewtonSelectedProbe z₁ z₂ z₃ m‖ := by sorry


end Couret.STROBO2TORS
