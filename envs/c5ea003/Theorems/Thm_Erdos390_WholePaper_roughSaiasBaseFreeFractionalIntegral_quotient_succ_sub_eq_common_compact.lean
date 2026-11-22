-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact
-- name    : Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:46:17.007572+00:00
-- url     : https://prove2.me/theorems/884b7a7b-d204-4a75-a0be-ed6583e72d10
-- title:
--   Common-range formula for a quotient drop and base increment
-- statement:
--   Let $1\le q_1\le q_0$ and $m\ge2$ be natural numbers with $\log q_0/\log m\le5$. Write $K(q,m,t)=D_\rho((\log q-\log t)/\log m)/\log m$ for the scaled Dickman kernel, where $D_\rho$ is the source-defined Dickman derivative, and $I(q,m)=\int_1^{m^5}\{t\}t^{-2}K(q,m,t)\,dt$ for its base-free fractional correction.
--
--   Then
--   $$I(q_1,m+1)-I(q_0,m)=\int_1^{m^5}\frac{\{t\}}{t^2}\bigl(K(q_1,m+1,t)-K(q_0,m,t)\bigr)\,dt.$$
--
--   The common cap permits variation estimates across changing natural quotients.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpVariation.lean#L354-L450

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact : Erdos390.RemainingAnalyticGoal008_025 := by sorry
