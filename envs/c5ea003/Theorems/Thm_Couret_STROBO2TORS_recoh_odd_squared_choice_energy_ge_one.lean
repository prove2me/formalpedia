-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_squared_choice_energy_ge_one
-- name    : Couret.STROBO2TORS.recoh_odd_squared_choice_energy_ge_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:55.613169+00:00
-- url     : https://prove2.me/theorems/046a6bb4-23fb-4402-8cae-2caaf78eb6a8
-- title:
--   Approximate complex centres select a norm at least one
-- statement:
--   For rational $s_j$, let $c_m^{\rm sq}(s)$ be the first $j<m$ with $s_j\ge9/4$, defaulting to zero. Let $m>0$, $e_j\in\mathbb R$, and actual and centre sequences $z_j,w_j\in\mathbb C$. On $j<m$, assume $|z_j|=e_j$, $s_j=|w_j|^2$ after rational-to-real conversion, and $|w_j-z_j|\le1/2$. Suppose either all $e_j=1$ or some $e_j\ge3$. Then
--
--   $$e_{c_m^{\rm sq}(s)}\ge1.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerSelection.lean#L268-L305, lines 268–305; source file SHA-256 4b170d730a51729f5ba927507b15a30bb6589eba29b9066d779b320d2f7bf524; theorem Couret.STROBO2TORS.recoh_odd_squared_choice_energy_ge_one

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_some
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_predicate_choice_spec
import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# Deterministic certified selection of an odd power

The executable search examines the rational approximations in ascending
index order, accepts the first value at least `3/2`, and falls back to index
zero.  Index `j` represents the odd character power `2*j+1`.

The contract uses an absolute error at most `1/2` on squared magnitude.
The root equations imply the dichotomy required to justify the fallback;
the selector never needs the hidden phases or an opposite-pair witness.
Constructing the rational approximations from a canonical square is a
separate obligation.  Extensionality below states the precise interface
that such a deterministic approximation procedure must satisfy.
-/

namespace Couret.STROBO2TORS

theorem recoh_odd_squared_choice_energy_ge_one
    (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ)
    (actual centre : ℕ → ℂ) (sqNorm : ℕ → ℚ)
    (henergy : ∀ j < m, ‖actual j‖ = energy j)
    (hsq : ∀ j < m, (sqNorm j : ℝ) = ‖centre j‖ ^ 2)
    (herror : ∀ j < m, ‖centre j - actual j‖ ≤ (1 / 2 : ℝ))
    (hdich : (∀ j < m, energy j = 1) ∨ ∃ j < m, 3 ≤ energy j) :
    1 ≤ energy (recohOddSquaredChoice m sqNorm) := by sorry




end Couret.STROBO2TORS
