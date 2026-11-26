-- Prove2me | Theorems.Thm_section5_hermite_roundCoord_norm_error
-- name    : section5_hermite_roundCoord_norm_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:25.815428+00:00
-- url     : https://prove2.me/theorems/60e6f4bb-d751-5216-a568-c3535e8a8d99
-- title:
--   One-dimensional Hermite grid sampling error
-- statement:
--   Let $D\in\mathbb N$, let $c\in\mathbb C^D$ satisfy $\sum_{k<D}|c_k|^2=1$, and let $M\ge1$ be an integer. Put $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and $r_M(x)=-R+\delta\lfloor(x+R)/\delta\rfloor$. For $F_c=\sum_{k<D}c_k\sqrt{\varphi}\,H_k/\sqrt{k!}$, where $\varphi$ is the standard Gaussian density,
--
--   $$\left(\int_{-R}^{R}|F_c(x)-F_c(r_M(x))|^2\,dx\right)^{1/2}\le\sqrt{\frac{16(D+1)}M}.$$
--
--   This is a uniform sampling estimate for normalized complex Hermite expansions on the finite grid window.
-- source:
--   Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D, one-dimensional sampling estimate surrounding Eq. (226). Formalization: Solutions/Section5HermiteWavefunctions.lean, lines 460–467.

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
import Theorems.Thm_section5_hermite_roundCoord_error
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_hermite_roundCoord_norm_error {D : ℕ} (c : Fin D → ℂ)
    (hc : ∑ k, ‖c k‖^2 = 1) (M : ℕ) (hM : 0 < M) :
    Real.sqrt (∫ x in (-QuantumLTF.Example.gridRadius M)..(QuantumLTF.Example.gridRadius M),
      ‖section5_complex_hermite_series c x-
        section5_complex_hermite_series c (QuantumLTF.Example.roundCoord M x)‖^2) ≤
          Real.sqrt (16*(D+1)/M) := by sorry
