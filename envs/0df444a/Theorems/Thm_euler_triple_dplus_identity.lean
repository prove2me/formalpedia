-- Prove2me | Theorems.Thm_euler_triple_dplus_identity
-- name    : euler_triple_dplus_identity
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:46:39.064114+00:00
-- url     : https://prove2.me/theorems/5abce2cd-18d4-44f4-8ef2-cc1b2f176648
-- title:
--   Regular extension of an Euler triple
-- statement:
--   Let $a,b,r\in\mathbb{N}$ with $ab+1=r^2$ and $c=a+b+2r$. Then the regular-quadruple operator gives $$d_+(a,b,c)=a+b+c+2abc+2r(a+r)(b+r)=4r(a+r)(b+r).$$ Hence every Euler triple extends to an Euler quadruple of the form $\{a,b,a+b+2r,4r(a+r)(b+r)\}$. Pure algebra; used in Section 8.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 8 (Euler quadruple form).

theorem euler_triple_dplus_identity (a b r : Nat) (h : a * b + 1 = r ^ 2) :
    a + b + (a + b + 2 * r) + 2 * a * b * (a + b + 2 * r)
      + 2 * r * (a + r) * (b + r) = 4 * r * (a + r) * (b + r) := by sorry
