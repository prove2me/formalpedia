-- Prove2me | Theorems.Thm_section5_hermite_deriv_integrable_sq
-- name    : section5_hermite_deriv_integrable_sq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:38.783306+00:00
-- url     : https://prove2.me/theorems/c8cc7a78-a103-482c-a0cd-265699cee622
-- title:
--   Square integrability of the derivative of a finite Hermite series
-- statement:
--   Write $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ and $\psi_k(x)=\sqrt{\phi(x)}H_k(x)/\sqrt{k!}$, where $H_k$ is the probabilists' Hermite polynomial. For $D\ge0$ and $c_0,\ldots,c_{D-1}\in\mathbb R$, put $F_c(x)=\sum_{k=0}^{D-1}c_k\psi_k(x)$. The explicitly represented derivative $F'_c=\frac12\sum_{k=0}^{D-1}c_k(\sqrt{k}\,\psi_{k-1}-\sqrt{k+1}\,\psi_{k+1})$ has integrable square:
--
--   $$
--   \int_{\mathbb R}|F'_c(x)|^2\,dx<\infty.
--   $$
--
--   The lowering term for $k=0$ is zero.
--
--   This ensures derivative-energy integrals of finite Hermite expansions are well defined.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5HermiteWavefunctions.lean, section5_hermite_deriv_integrable_sq, lines 198–218.

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
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_hermite_deriv_integrable_sq {D : ℕ} (c : Fin D → ℝ) :
    Integrable (fun x => (section5_hermite_series_deriv c x)^2) := by sorry
