-- Prove2me | Theorems.Thm_section5_hermite_derivative_energy
-- name    : section5_hermite_derivative_energy
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:06.848375+00:00
-- url     : https://prove2.me/theorems/34957353-ecf3-496a-9ba0-85359fb57ca7
-- title:
--   Derivative energy of a finite Hermite expansion
-- statement:
--   Let $D\in\mathbb N$, let $c_0,\ldots,c_{D-1}\in\mathbb R$, and let $\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}$. For the probabilists' Hermite polynomials $H_k$, put $\psi_k(x)=\sqrt{\varphi(x)}H_k(x)/\sqrt{k!}$ and $F_c(x)=\sum_{k<D}c_k\psi_k(x)$. Then
--
--   $$\int_{\mathbb R}|F_c'(x)|^2\,dx\le(D+1)\sum_{k<D}c_k^2.$$
--
--   This controls the derivative energy uniformly over the finite Hermite subspace and provides an input to its discretization estimates.
-- source:
--   Original auxiliary Hermite-energy estimate for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5HermiteWavefunctions.lean, lines 220–245; wavefunction and derivative conventions are defined in the same file.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_section5_hermite_deriv_integrable_sq
import Theorems.Thm_section5_hermite_lower_integral_sq
import Theorems.Thm_section5_wave_sum_integrable_product
import Theorems.Thm_section5_wave_sum_product_integral
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_hermite_derivative_energy {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, (section5_hermite_series_deriv c x)^2) ≤ (D+1)*∑ k, (c k)^2 := by sorry
