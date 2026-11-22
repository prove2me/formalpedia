-- Prove2me | Theorems.Thm_Erdos390_Full_ContinuumCellGraph_ArithmeticGaugeOrdinary_IntervalMesh_ordinary_split_arithmetic_projected_raw_bound_compact
-- name    : Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:55:35.301764+00:00
-- url     : https://prove2.me/theorems/482525b8-2388-4897-8ee3-224a827c7099
-- title:
--   Many-low ordinary inverse on the arithmetic raw gauge
-- statement:
--   Let a finite nonempty interval mesh be split into Low and nonempty High. Assume the covariance kernel product bound Cst, a positive interior quotient gap κ, positive high anchor mass A, high centers between a_min>0 and a_max≥0, low centers at most c₀≥0, and low and total lengths at most L₀,L≥0. Let positive arithmetic weights H_i and centers α_i≤α_max define the raw gauge. Assume the mixed low/high gauge ratio is bounded by g; low continuum diagonal error is at most d<1; continuum row residual is bounded by r≥0; arithmetic-versus-continuum raw row error is bounded by e‖b‖ with e≥0. With S=∑H_iα_i², assume α_max∑H_iα_i≤RS, R≥0, and α_max∑|H_iα_i−M.harmonicMass_i M.center_i|≤ρS with ρ≤1/2. Define ε=(r+Cc₀L)/(1−d), c=(1−d)⁻¹ and C₀=max(c,a_max[2(κA)⁻¹(a_min⁻¹+CL₀c)+gc]). Assume max(ε,a_max[2(κA)⁻¹(Cc₀L₀/a_min+CL₀ε)+gε])≤1/2 and 4C₀(1+R)(e+r)≤1/2. Then the projected arithmetic raw operator T satisfies the following bound. It is independent of the number and least center of the low cells.
--
--   $$\|b\|_\infty\le 8C_0\|Tb\|_\infty.$$
--
--   This compact declaration is definitionally identical to the original fully quantified statement; the named proposition preserves every hypothesis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/ContinuumManyLowArithmeticGaugeOrdinary.lean#L192-L637

import Definitions.Def_erdos390_analytic_compact_goals

universe u_1 u_2 u_3

theorem Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound_compact : Erdos390.AnalyticCompactGoal001.{u_1, u_2, u_3} := by sorry
