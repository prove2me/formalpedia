-- Prove2me | Theorems.Thm_Erdos390_WholePaper_exists_uniform_roughFixedHead_friableCount_shift_bound_compact
-- name    : Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:43:07.946284+00:00
-- url     : https://prove2.me/theorems/a56fafed-9199-4946-af2d-a900cd64369b
-- title:
--   Uniform fixed-head divisor shift for friable counts
-- statement:
--   Fix a natural head cutoff $W$, and let $P_W$ be its rough-head modulus. There exist $K>0$ and $Y_0\in\mathbb N$ such that for all natural $X,y,d$ with $y\ge Y_0$, $d\mid P_W$, $d\le X$ and $\log X\le5\log y$,
--   $$\left|\Psi(\lfloor X/d\rfloor,y)-\frac{\Psi(X,y)}d\right|\le\frac{KX}{d\log y}+3.$$
--   Here $d$ ranges over the positive divisors of $P_W$ and $\Psi$ counts friable integers. The constants are uniform across the fixed finite divisor family.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughFixedHeadFriableShift.lean#L243-L366

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound_compact : Erdos390.RemainingAnalyticGoal008_013 := by sorry
