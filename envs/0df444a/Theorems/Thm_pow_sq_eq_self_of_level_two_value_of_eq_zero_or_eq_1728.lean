-- Prove2me | Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
-- name    : pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/c19ddf5c-0ffb-5060-b62a-f5593c8e66cd
-- title:
--   Legendre parameters over j=0 and j=1728 are q²-fixed
-- statement:
--   Let $k$ be a field whose characteristic is a prime $q$ with $5 \le q$, let $a \in k$ satisfy $a = 0$ or $a = 1728$, and let $l \in k$ satisfy the polynomial identity
--   $$a\,\bigl((16l)^2 (16l-1)^2\bigr) = 256\bigl((16l)^2 - 16l + 1\bigr)^3 .$$
--   Then $l^{q^2} = l$. Thus, writing $\lambda = 16 l$, the assertion is that any solution in $k$ of the denominator-cleared equation $j(\lambda) = a$ for the Legendre $j$-invariant $j = 256(\lambda^2-\lambda+1)^3/\bigl(\lambda^2(\lambda-1)^2\bigr)$, with $a$ equal to $0$ or to $1728$, is fixed by the square of the Frobenius endomorphism of $k$, i.e. lies in the subfield of $k$ of elements satisfying $x^{q^2} = x$. No hypothesis of perfectness, finiteness or algebraic closedness is imposed on $k$.
--
--   The equation is the division-free form of $j(\lambda) = a$ for the Legendre parameter $\lambda = 16l$, and the conclusion is the $\mathbb{F}_{q^2}$-rationality of the level-two parameter above the two exceptional $j$-invariants $0$ and $1728$. It feeds the rationality hypotheses used in the local analysis at the nodes of the $\lambda$-line, being cited by the localisation results [`ModularCurve.LambdaNodeLocalized.eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem`](thm.html#ModularCurve.LambdaNodeLocalized.eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem), [`ModularCurve.LambdaNodeLocalized.exists_level_two_value_sub_const_mem_of_isMaximal`](thm.html#ModularCurve.LambdaNodeLocalized.exists_level_two_value_sub_const_mem_of_isMaximal) and [`ModularCurve.LambdaNodeLocalized.exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728`](thm.html#ModularCurve.LambdaNodeLocalized.exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728), among others.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
    {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (l : k)
    (hl : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    l ^ (q ^ 2) = l := by sorry
