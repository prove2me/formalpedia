-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_newton_selected_probe_norm
-- name    : Couret.STROBO2TORS.recoh_newton_selected_probe_norm
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:11.873089+00:00
-- url     : https://prove2.me/theorems/dc32697e-fc2c-4d34-9ef1-548eefd4fb2d
-- title:
--   The certified Newton choice has amplitude at least one half
-- statement:
--   Let $z_1,z_2,z_3\in\mathbb C$ have modulus one, put $s=z_1+z_2+z_3$, $t=z_1^3+z_2^3+z_3^3$, and $p=z_1z_2z_3$. For $m\in\mathbb Q$, define $\mu(m)=1$ when $m\ge3/8$ and $\mu(m)=3$ otherwise. If $|m-|s|^2|\le1/8$, then
--
--   $$|z_1^{\mu(m)}+z_2^{\mu(m)}+z_3^{\mu(m)}|\ge1/2.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohTripleNewton.lean#L163-L187, lines 163–187; source file SHA-256 c0dfe04ad32a6cb240d859da6d7a72431007a71855a11b54c052d91aa4f8724e; theorem Couret.STROBO2TORS.recoh_newton_selected_probe_norm

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_cubes_norm_lower
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

theorem recoh_newton_selected_probe_norm (z₁ z₂ z₃ : ℂ) (m : ℚ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (hcert : |(m : ℝ) - ‖z₁ + z₂ + z₃‖ ^ 2| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ ‖recohNewtonSelectedProbe z₁ z₂ z₃ m‖ := by sorry




end Couret.STROBO2TORS
