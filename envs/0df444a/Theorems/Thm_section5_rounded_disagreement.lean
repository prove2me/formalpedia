-- Prove2me | Theorems.Thm_section5_rounded_disagreement
-- name    : section5_rounded_disagreement
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:22.91062+00:00
-- url     : https://prove2.me/theorems/ee8a215c-c0ad-5467-8049-90b4f42f1dfc
-- title:
--   Disagreement of two rounded Gaussian halfspaces
-- statement:
--   Let $w,u\in\mathbb R^n$ be unit vectors and let $M\ge1$ be an integer. Let $r_M$ round coordinatewise down on the centered lattice of spacing $\sqrt{4\pi/M}$ and radius parameter $\sqrt{\pi M}$. With $f_v(x)=\operatorname{sgn}\langle v,x\rangle$ and sign $+1$ at zero,
--
--   $$\Pr_{X\sim N(0,I_n)}\{f_w(r_M(X))\ne f_u(r_M(X))\}\le\frac{\|w-u\|_2}{2}+2\sqrt{8n/M}.$$
--
--   This controls the disagreement of two candidate directions after the same finite-grid rounding.
-- source:
--   Original rounded-disagreement auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5RoundedOrientation.lean, lines 41–64. Its Gaussian disagreement foundation is the reused accepted proof by kmehltretter82, submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), credited in Solutions/Section5GaussianDisagreementFoundation.lean.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_rounding_label_probability
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_rounded_disagreement {n M : ℕ} (hM : 1 ≤ M)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 (roundVec M x) ≠ ltf u 0 (roundVec M x)} ≤
        ‖w-u‖/2+2*Real.sqrt (8*n/M) := by sorry
