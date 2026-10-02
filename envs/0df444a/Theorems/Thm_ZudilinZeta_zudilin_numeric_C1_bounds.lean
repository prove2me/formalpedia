-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_bounds
-- name    : ZudilinZeta.zudilin_numeric_C1_bounds
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T17:09:01.052586+00:00
-- url     : https://prove2.me/theorems/27923803-1c03-4ec6-ae21-2c3e3f00d593
-- title:
--   Certified enclosure of the arithmetic constant C₁ for Zudilin’s parameters
-- statement:
--   For Zudilin’s concrete parameter tuple $(r,q)=(3,13)$ with $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$ and $\eta_j=25+j$ for $4\le j\le13$, the arithmetic growth constant defined using the periodic floor minimum $\phi$ and the digamma derivative satisfies
--   $$226.24944266\le C_1<226.24944267.$$
--   Here the elementary lcm contribution is $3\cdot35+34+8\cdot33=403$, and the cutoff in the second integral defining $C_1$ is $1/33$. This is the arithmetic half of the numerical comparison appearing in the proof of the irrationality theorem.
-- source:
--   W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Proposition 5 and proof of Theorem 3, printed pp. 34–35; the analytic constant is C0, and that paper denotes the mission arithmetic constant C1 by C2. Also One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), 774–776.

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem zudilin_numeric_C1_bounds :
    226.24944266 ≤ C1 params13 ∧ C1 params13 < 226.24944267 := by sorry
end ZudilinZeta
