-- Prove2me | Theorems.Thm_isSMulRegular_iff_of_free
-- name    : isSMulRegular_iff_of_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/5b570de0-8f6a-50eb-a522-dde62bdba955
-- title:
--   Regularity on a nonzero free module detects non-zero-divisors
-- statement:
--   Let $R$ be a commutative ring and $M$ an $R$-module which is free (as an $R$-module, via Mathlib's `Module.Free`) and nontrivial, i.e. $M$ has at least two elements, equivalently $M \neq 0$. Let $r \in R$. The assertion is the equivalence of `IsSMulRegular M r` and `IsSMulRegular R r`: the map $M \to M$, $m \mapsto r \cdot m$, is injective if and only if the map $R \to R$, $x \mapsto r x$, is injective, i.e. $r$ is a non-zero-divisor of $R$. Both sides are stated as injectivity of the scalar-multiplication map, so no Noetherian, finiteness or local hypothesis is imposed, and the index set of the basis is arbitrary; nontriviality of $M$ is exactly what is needed for the forward implication.
--
--   This is the standard fact that the non-zero-divisors acting on a nonzero free module $R^{(I)}$ are precisely the non-zero-divisors of $R$. It serves as the base case of the comparison between weakly regular sequences on $R$ and on a free $R$-module, and is cited in the project by [`RingTheory.Sequence.isWeaklyRegular_of_free_aux`](thm.html#RingTheory.Sequence.isWeaklyRegular_of_free_aux), the ingredient used for depth estimates for the patched module, which is free over a power-series ring in Taylor–Wiles–Kisin patching.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_isSMulRegular_iff_of_free.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem isSMulRegular_iff_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by sorry
