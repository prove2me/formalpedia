-- Prove2me | Theorems.Thm_section5_multivariate_sampling_227
-- name    : section5_multivariate_sampling_227
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:20:13.893347+00:00
-- url     : https://prove2.me/theorems/90266905-f05a-4478-bd26-9b27c21e265e
-- title:
--   Multivariate Hermite sampling bound (227)
-- statement:
--   Let $n,D,M\in\mathbb N$ with $M\ge1$ and $M\ge64n^2(D+1)$. Put $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and $r_M(x)=-R+\delta\lfloor(x+R)/\delta\rfloor$, applied coordinatewise. Let $\psi_k=\sqrt{\varphi}\,H_k/\sqrt{k!}$ be the normalized Hermite wavefunctions. For complex coefficients indexed by $a\in\{0,\ldots,D-1\}^n$ with $\sum_a|c_a|^2=1$, put $F_c(x)=\sum_ac_a\prod_i\psi_{a_i}(x_i)$. Then
--
--   $$\left(\int_{(-R,R]^n}|F_c(x)-F_c(r_M(x))|^2\,dx\right)^{1/2}\le2n\sqrt{\frac{16(D+1)}M}.$$
--
--   This is the uniform multivariate sampling estimate for finite Hermite superpositions.
-- source:
--   Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D, Eq. (227). Formalization: Solutions/Section5MultivariateSampling.lean, lines 105–127.

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
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_complex_series_integral_sq
import Theorems.Thm_section5_hermite_roundCoord_error
import Theorems.Thm_section5_hybrid_linear_bound
import Theorems.Thm_section5_tensor_synthesis_error
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem section5_multivariate_sampling_227 (n D M : ℕ) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (c : (Fin n → Fin D) → ℂ)
    (hc : ∑ a, ‖c a‖^2 = 1) :
    Real.sqrt (∫ x : Fin n → ℝ,
      ‖(∑ a, c a*∏ i, section5_complex_wave D (a i) (x i))-
        (∑ a, c a*∏ i, section5_complex_wave D (a i) (roundCoord M (x i)))‖^2
      ∂(Measure.pi (fun _ : Fin n => section5_window_measure M))) ≤
        2*n*Real.sqrt (16*(D+1)/M) := by sorry
