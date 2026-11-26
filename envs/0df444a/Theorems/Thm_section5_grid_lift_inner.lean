-- Prove2me | Theorems.Thm_section5_grid_lift_inner
-- name    : section5_grid_lift_inner
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:59.94413+00:00
-- url     : https://prove2.me/theorems/b90055b4-26f6-4992-bdae-5c6b34c123e5
-- title:
--   Inner-product preservation by the finite-grid lift
-- statement:
--   Let $n,M\in\mathbb N$ with $M\ge1$, $\delta=\sqrt{4\pi/M}$, and $R=M\delta/2$. For measurable $F,G:\mathbb R^n\to\mathbb C$, define the cell lifts $L_F(x)=1_{(-R,R]^n}(x)F(r_M(x))$ and $L_G$ similarly, with $r_M$ the centered coordinatewise grid rounding. Define grid vectors $v_F(j)=\sqrt{\delta^n}F(-R+\delta j)$ for $j\in\{0,\ldots,M-1\}^n$, and similarly $v_G$. Then
--
--   $$\langle L_F,L_G\rangle_{L^2(\mathbb R^n)}=\langle v_F,v_G\rangle_{\ell^2}.$$
--
--   The identity makes the cell-function and finite-register descriptions compatible as inner-product spaces.
-- source:
--   Original grid-isometry auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5GridIsometry.lean, lines 93–124.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Mathlib
import Theorems.Thm_section5_finite_grid_quadrature
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example

theorem section5_grid_lift_inner (n M : ℕ) (hM : 0 < M)
    (F G : (Fin n → ℝ) → ℂ) (hF : Measurable F) (hG : Measurable G) :
    inner ℂ ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F))
      ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G)) =
      inner ℂ (section5_grid_vector n M F) (section5_grid_vector n M G) := by sorry
