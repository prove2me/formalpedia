-- Prove2me | Theorems.Thm_euler_triple_square_identities
-- name    : euler_triple_square_identities
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:46:39.366311+00:00
-- url     : https://prove2.me/theorems/fbc14905-7ab0-4ded-9a78-a806268f791e
-- title:
--   Square witnesses in an Euler triple
-- statement:
--   Let $a,b,r\in\mathbb{N}$ with $ab+1=r^2$ and put $c=a+b+2r$ (the Euler extension). Then $$ac+1=(a+r)^2\quad\text{and}\quad bc+1=(b+r)^2,$$ i.e. the Euler triple carries explicit square witnesses. Pure algebra; used in Section 8 (Theorem 7) with $s=a+r$ and $t=b+r$.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 8, Theorem 7 (identities $s=a+r$, $t=b+r$).

theorem euler_triple_square_identities (a b r : Nat) (h : a * b + 1 = r ^ 2) :
    a * (a + b + 2 * r) + 1 = (a + r) ^ 2 ∧ b * (a + b + 2 * r) + 1 = (b + r) ^ 2 := by sorry
