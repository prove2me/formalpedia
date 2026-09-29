-- Prove2me | Theorems.Thm_diophantine_degree_one_parametrization
-- name    : diophantine_degree_one_parametrization
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:46:39.57935+00:00
-- url     : https://prove2.me/theorems/2e9a17fa-9e18-4cfa-bbfb-024597e6abb3
-- title:
--   Signed parametrization for degree one
-- statement:
--   Let $a,b,r$ be integers with $ab+1=r^2$ and let $s=\pm 1$. Put $d=a+b+2sr$ (the signed form of $d_{-1}=a+b\pm 2r$). Then $$(r+sa)^2=ad+1,\qquad (b+sr)^2=bd+1,$$ and the regular-quadruple value satisfies $$d_+(a,d,b)=a+d+b+2adb+2(r+sa)r(b+sr)=4r(r+sa)(b+sr),$$ i.e. $c=4r(r\pm a)(b\pm r)$ with correlated signs. Stated over $\mathbb{Z}$ to avoid truncated subtraction. This is the structural computation in the proof of Theorem 8; only the $+$ case has $d\ge 0$.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 9, proof of Theorem 8 ($d_{-1}=a+b\pm 2r$, $c=d_+(a,d_{-1},b)$).

theorem diophantine_degree_one_parametrization (a b r s : Int)
    (hs : s = 1 ∨ s = -1) (hr : a * b + 1 = r ^ 2) :
    (r + s * a) ^ 2 = a * (a + b + 2 * s * r) + 1 ∧
    (b + s * r) ^ 2 = b * (a + b + 2 * s * r) + 1 ∧
    a + (a + b + 2 * s * r) + b + 2 * a * (a + b + 2 * s * r) * b
      + 2 * (r + s * a) * r * (b + s * r)
      = 4 * r * (r + s * a) * (b + s * r) := by sorry
