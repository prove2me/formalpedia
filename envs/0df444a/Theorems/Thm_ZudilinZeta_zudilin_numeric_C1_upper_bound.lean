-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_upper_bound
-- name    : ZudilinZeta.zudilin_numeric_C1_upper_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T18:09:10.908989+00:00
-- url     : https://prove2.me/theorems/45ff3047-3efc-4331-9a8a-7ef8f49028d3
-- title:
--   A certified sufficient upper bound for Zudilin’s arithmetic constant
-- statement:
--   For Zudilin’s parameter tuple $(r,q)=(3,13)$, $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$, and $\eta_j=25+j$ for $4\le j\le13$, the arithmetic exponential-rate constant satisfies
--   $$C_1<\frac{455}{2}=227.5.$$
--   Together with the certified analytic bound $C_0\ge227.58019641$, this supplies the strict inequality $C_1<C_0$ required by the irrationality criterion.
-- source:
--   W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Proposition 5 and proof of Theorem 3, printed pp. 34–36. This paper calls the mission arithmetic constant C2. The coarser upper bound here follows from certified finite truncation of the established periodic floor integral.

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem zudilin_numeric_C1_upper_bound :
    C1 params13<227.5 := by sorry
end ZudilinZeta
