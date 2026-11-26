-- Prove2me | Theorems.Thm_section5_complex_series_integral_sq
-- name    : section5_complex_series_integral_sq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:41.598816+00:00
-- url     : https://prove2.me/theorems/8db87dbd-c812-54fc-800a-38da5988834b
-- title:
--   Parseval identity for a finite complex Hermite expansion
-- statement:
--   Write $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ and $\psi_k(x)=\sqrt{\phi(x)}H_k(x)/\sqrt{k!}$, where $H_k$ is the probabilists' Hermite polynomial. For every natural number $D$ and coefficients $c_0,\ldots,c_{D-1}\in\mathbb C$,
--
--   $$
--   \int_{\mathbb R}\left|\sum_{k=0}^{D-1}c_k\psi_k(x)\right|^2\,dx=\sum_{k=0}^{D-1}|c_k|^2.
--   $$
--
--   This identifies the squared continuous norm of a finite Hermite expansion with the squared coefficient norm.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5MultivariateSampling.lean, section5_complex_series_integral_sq, lines 29–45.

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
import Theorems.Thm_section5_wave_sum_integrable_product
import Theorems.Thm_section5_wave_sum_product_integral
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem section5_complex_series_integral_sq {D : ℕ} (c : Fin D → ℂ) :
    (∫ x : ℝ, ‖section5_complex_hermite_series c x‖^2) = ∑ k, ‖c k‖^2 := by sorry
