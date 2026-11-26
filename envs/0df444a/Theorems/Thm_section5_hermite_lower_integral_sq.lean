-- Prove2me | Theorems.Thm_section5_hermite_lower_integral_sq
-- name    : section5_hermite_lower_integral_sq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:35.203011+00:00
-- url     : https://prove2.me/theorems/9d41a712-27a3-5828-9100-ae5ead7ac046
-- title:
--   Squared norm of the lowering part of a Hermite expansion
-- statement:
--   Write $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ and $\psi_k(x)=\sqrt{\phi(x)}H_k(x)/\sqrt{k!}$, where $H_k$ is the probabilists' Hermite polynomial. For $D\ge0$ and real coefficients $c_0,\ldots,c_{D-1}$, define $L_c(x)=\sum_{k=0}^{D-1}c_k\sqrt{k}\,\psi_{k-1}(x)$, with the $k=0$ term zero. Then
--
--   $$
--   \int_{\mathbb R}L_c(x)^2\,dx=\sum_{k=0}^{D-1}k c_k^2.
--   $$
--
--   This computes the energy of the lowering component used in derivative estimates.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5HermiteWavefunctions.lean, section5_hermite_lower_integral_sq, lines 159–187.

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
import Theorems.Thm_section5_wave_sum_product_integral
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_hermite_lower_integral_sq {D : ℕ} (c : Fin D → ℝ) :
    (∫ x : ℝ, (section5_hermite_lower c x)^2) = ∑ k, (c k)^2*(k:ℕ) := by sorry
