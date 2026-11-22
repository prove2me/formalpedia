-- Prove2me | Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
-- name    : Erdos390.Full.DickmanBasic.rho_pos_on_zero_five
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T13:49:55.188021+00:00
-- url     : https://prove2.me/theorems/ea3f6f6b-a052-4773-92b2-d74601c689a9
-- title:
--   Positivity of the finite Dickman function on the required range
-- statement:
--   Let $\rho_0(x)=1$ for every real $x$, and define recursively
--
--   $$\rho_{n+1}(x)=\begin{cases}1&x\le1,\\1-\int_1^x\frac{\rho_n(t-1)}{\max(t,1)}\,dt&x>1.\end{cases}$$
--
--   For the fifth approximant $\rho=\rho_5$, every real $x\in[0,5]$ satisfies
--
--   $$\rho(x)>0.$$
--
--   This gives positivity on the entire finite range used by the Poisson–Dickman construction, in particular the nonzero normalization at $x=9/2$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/DickmanBasic.lean#L321-L381

import Definitions.Def_erdos390_dickman_step_function

theorem Erdos390.Full.DickmanBasic.rho_pos_on_zero_five :
    ∀ {x : ℝ} (hx0 : 0 ≤ x) (hx5 : x ≤ 5), 0 < Erdos390.Full.DickmanBasic.rho x := by sorry
