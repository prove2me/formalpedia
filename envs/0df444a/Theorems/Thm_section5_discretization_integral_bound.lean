-- Prove2me | Theorems.Thm_section5_discretization_integral_bound
-- name    : section5_discretization_integral_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:25:28.683433+00:00
-- url     : https://prove2.me/theorems/131ef087-42dc-455c-8c1f-530817d7fd56
-- title:
--   Gaussian mean-square error from rounding a homogeneous threshold
-- statement:
--   For a natural grid parameter $M$, set $\Delta_M=\sqrt{4\pi/M}$, $R_M=M\Delta_M/2$, and $r_M(t)=-R_M+\Delta_M\lfloor(t+R_M)/\Delta_M\rfloor$. For $w\in\mathbb R^n$, let $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$, with the sign at zero equal to $1$. For $M\ge1$ and $\|w\|=1$, coordinatewise rounding satisfies
--
--   $$
--   \mathbb E_{X\sim N(0,I_n)}\left[(f_w(X)-f_w(r_M(X)))^2\right]\le4\sqrt{8n/M}.
--   $$
--
--   This controls the Gaussian squared label error introduced by grid discretization.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GaussianRounding.lean, section5_discretization_integral_bound, lines 146–177.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
import Theorems.Thm_section5_discretization_measurable
import Theorems.Thm_section5_gaussian_inner_strip
import Theorems.Thm_section5_roundCoord_error
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_discretization_integral_bound {n M : ℕ} (hM : 1 ≤ M)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    ∫ x, (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ 4*Real.sqrt (8*n/M) := by sorry
