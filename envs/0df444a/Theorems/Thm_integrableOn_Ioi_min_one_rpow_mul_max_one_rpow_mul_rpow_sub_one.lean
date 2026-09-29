-- Prove2me | Theorems.Thm_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
-- name    : integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/440967e3-7418-5b57-8f70-3356cfca131e
-- title:
--   Integrability of min(1,r)ᵖmax(1,r)^{-q}rᶜ⁻¹ on (0,∞)
-- statement:
--   Let $p$, $q$, $c$ be real numbers subject to the two inequalities $0 < p + c$ and $c < q$. The assertion is that the function
--   $$r \mapsto (\min(1,r))^{p}\,(\max(1,r))^{-q}\,r^{c-1},$$
--   where all three powers are real exponentiation of real numbers, is integrable on the open half-line $(0,\infty)$ with respect to Lebesgue measure, in the sense of `MeasureTheory.IntegrableOn`: it is almost everywhere measurable on $(0,\infty)$ and its absolute value has finite integral over that set. Note that the exponent appearing in the statement is $-q$, so the hypothesis $c < q$ is exactly the condition $c - q - 1 < -1$ governing convergence at $+\infty$, while $0 < p + c$ is the condition $p + c - 1 > -1$ governing convergence at $0$; no sign or size assumption is placed on $p$, $q$ or $c$ individually.
--
--   This is the elementary one-variable convergence criterion for the model archimedean torus integral: in polar coordinates $d^\times r = dr/r$, a Whittaker-type integrand bounded by $\min(1,r)^{p}$ near $0$ and by $\max(1,r)^{-q}$ near $\infty$ reduces to precisely this integral, the two hypotheses being the abscissa condition and the prescribed order of decay. It is used in the analysis of the $S$-part of a Rankin–Selberg integral ([`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery)) and in an integrability statement for idelic measures ([`NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg`](thm.html#NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
    (p q c : ℝ) (hpc : 0 < p + c) (hcq : c < q) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioi 0) := by sorry
