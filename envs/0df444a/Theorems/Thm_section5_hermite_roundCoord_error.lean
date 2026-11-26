-- Prove2me | Theorems.Thm_section5_hermite_roundCoord_error
-- name    : section5_hermite_roundCoord_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:08.57375+00:00
-- url     : https://prove2.me/theorems/1f6d9537-32ea-504f-9782-c7ac4e6b47bd
-- title:
--   Integrated rounding error for a complex Hermite wavefunction sum
-- statement:
--   Let D be natural, c_0,…,c_(D−1) complex, M>0 natural, δ=√(4π/M), R=Mδ/2, and let ψ_k(x)=√φ(x)He_k(x)/√(k!) for standard Gaussian density φ. Put F(x)=Σ_(k<D)c_kψ_k(x), and let round_M be the public left-grid rounding map with spacing δ. Then $$\int_{-R}^R|F(x)-F(\operatorname{round}_M(x))|^2\,dx\le\frac{16(D+1)}M\sum_{k<D}|c_k|^2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteWavefunctions.lean, lines 439–444.

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
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_phi
import Theorems.Thm_Aux_w_53_hermite_x_mul_h1D_eq
import Theorems.Thm_section5_grid_cell_quadrature
import Theorems.Thm_section5_grid_sampling_integral
import Theorems.Thm_section5_hermite_deriv_integrable_sq
import Theorems.Thm_section5_hermite_derivative_energy
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_hermite_roundCoord_error {D : ℕ} (c : Fin D → ℂ)
    (M : ℕ) (hM : 0 < M) :
    (∫ x in (-QuantumLTF.Example.gridRadius M)..(QuantumLTF.Example.gridRadius M),
      ‖section5_complex_hermite_series c x-
        section5_complex_hermite_series c (QuantumLTF.Example.roundCoord M x)‖^2) ≤
          16*(D+1)/M*∑ k, ‖c k‖^2 := by sorry
