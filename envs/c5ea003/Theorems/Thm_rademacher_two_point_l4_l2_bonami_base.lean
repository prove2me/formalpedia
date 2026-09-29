-- Prove2me | Theorems.Thm_rademacher_two_point_l4_l2_bonami_base
-- name    : rademacher_two_point_l4_l2_bonami_base
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T02:33:19.504902+00:00
-- url     : https://prove2.me/theorems/623cb0cb-45bf-447d-91c8-a4de24118d10
-- statement:
--   The scalar **two-point (4,2)-hypercontractive (Bonami) base inequality** for a single uniform Rademacher sign $x\in\{\pm1\}$. Writing $\mathbb E[f]=\tfrac12(f(+1)+f(-1))$ for the two-point average, this asserts
--
--   $$\mathbb Eig[(a+bx)^4ig]\;\le\;\Big(\mathbb Eig[(a+\sqrt3\,b\,x)^2ig]\Big)^2$$
--
--   for all real $a,b$. Expanding the averages gives $\mathbb E[(a+bx)^4]=	frac12ig((a+b)^4+(a-b)^4ig)=a^4+6a^2b^2+b^4$ and $\mathbb E[(a+\sqrt3 b x)^2]=	frac12ig((a+\sqrt3 b)^2+(a-\sqrt3 b)^2ig)=a^2+3b^2$, so the inequality is equivalent to $a^4+6a^2b^2+b^4\le(a^2+3b^2)^2=a^4+6a^2b^2+9b^4$, i.e. $0\le 8b^4$. This is the $q=4$, $n=1$ base case of Bonami/Beckner hypercontractivity; the constant $\sqrt3=\sqrt{q-1}$ is sharp. It is the per-coordinate brick that tensorizes to the bilinear Rademacher-chaos $(4,2)$ inequality.
-- source:
--   O’Donnell, *Analysis of Boolean Functions* (CUP 2014), Ch. 9, §9.1 (the two-point / Bonami–Beckner base case of hypercontractivity); A. Bonami, Ann. Inst. Fourier 20 (1970) 335–402; W. Beckner, Ann. of Math. 102 (1975) 159–182. Base case for the bilinear Rademacher-chaos (4,2) inequality (de la Peña–Montgomery-Smith 1995 Lemma 2 / Kwapień–Szulga 1991 eq. 1.4).

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem rademacher_two_point_l4_l2_bonami_base (a b : ℝ) :
    (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      ≤ ((((a + Real.sqrt 3 * b) ^ 2 + (a - Real.sqrt 3 * b) ^ 2) / 2)) ^ 2 := by sorry
