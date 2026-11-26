-- Prove2me | Theorems.Thm_section5_grid_lift_norm
-- name    : section5_grid_lift_norm
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:15.795712+00:00
-- url     : https://prove2.me/theorems/cbbf434f-dae3-4c33-9914-56717c661c62
-- title:
--   Isometry between grid vectors and cell-constant functions
-- statement:
--   Let n,M be natural numbers with M>0 and let F:R^n→C be measurable. Put δ=√(4π/M), R=Mδ/2, and g_j=(−R+j_iδ)_i for j∈{0,…,M−1}^n. Let L(F) be F evaluated at coordinatewise rounded grid points within (−R,R]^n and zero outside. Its Lebesgue L² norm equals the Euclidean norm of the grid vector V_j=√(δ^n)F(g_j): $$\|L(F)\|_{L^2}=\left(\sum_j\delta^n|F(g_j)|^2\right)^{1/2}=\|V\|_2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5GridIsometry.lean, lines 76–79.

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
import Theorems.Thm_section5_l2_norm_sq
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example

theorem section5_grid_lift_norm (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    ‖(section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)‖ =
      ‖section5_grid_vector n M F‖ := by sorry
