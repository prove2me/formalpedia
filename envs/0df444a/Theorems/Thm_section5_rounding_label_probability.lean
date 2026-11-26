-- Prove2me | Theorems.Thm_section5_rounding_label_probability
-- name    : section5_rounding_label_probability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:25.480215+00:00
-- url     : https://prove2.me/theorems/5e524a76-d2ed-5e7e-8cde-5aa531e6d955
-- title:
--   Gaussian threshold-label error caused by grid rounding
-- statement:
--   Let $n\in\mathbb N$, let $M\ge1$ be an integer, and let $w\in\mathbb R^n$ have unit norm. Set $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and $r_M(x)_i=-R+\delta\lfloor(x_i+R)/\delta\rfloor$. For $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, with sign $+1$ at zero,
--
--   $$\Pr_{X\sim N(0,I_n)}\{f_w(X)\ne f_w(r_M(X))\}\le\sqrt{8n/M}.$$
--
--   This quantifies the label error induced by global coordinatewise lattice rounding.
-- source:
--   Original label-probability consequence of the Section 5 discretization estimates, Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5RoundedOrientation.lean, lines 22–39.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Mathlib
import Theorems.Thm_section5_discretization_integral_bound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_rounding_label_probability {n M : ℕ} (hM : 1 ≤ M)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 x ≠ ltf w 0 (roundVec M x)} ≤ Real.sqrt (8*n/M) := by sorry
