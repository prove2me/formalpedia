-- Prove2me | Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
-- name    : ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/48c80f27-258e-54b9-b250-a51cc8c11c43
-- title:
--   Cyclic subgroups of order n in (ℤ/n)² number ψ(n)
-- statement:
--   Let $n$ be a natural number, assumed nonzero. Consider the additive group $\mathbb{Z}/n \times \mathbb{Z}/n$ and the set of its additive subgroups $H$ that are cyclic as additive groups and satisfy $\mathrm{card}(H) = n$, this set being taken as the subtype of `AddSubgroup (ZMod n × ZMod n)` cut out by those two conditions. The theorem asserts that the cardinality of this set of subgroups equals [`ModularCurve.dedekindPsi n`](def/ModularCurve_X0.html#L201), which is defined in the project as the sum $\sum_{d \mid n,\ d \text{ squarefree}} n/d$ over the squarefree divisors $d$ of $n$, the quotients being natural-number division. Thus $(\mathbb{Z}/n)^2$ has exactly $\psi(n)$ cyclic subgroups of order $n$, where $\psi$ is the Dedekind psi function in the above divisor-sum form, agreeing with $n \prod_{p \mid n}(1 + 1/p)$. Cardinalities are taken as `Nat.card`, so the assertion includes implicitly that the set of such subgroups is finite, the value $\psi(n)$ being nonzero.
--
--   Such subgroups are precisely the cyclic direct summands of rank one of $(\mathbb{Z}/n)^2$, equivalently the points of the projective line $\mathbb{P}^1(\mathbb{Z}/n)$, so the count is the number of $\Gamma_0(n)$-level structures on a pair of generators of $n$-torsion, i.e. the degree of $X_0(n) \to X(1)$. It is used in the project to transfer the count to torsion subgroups of abstract abelian groups isomorphic to $(\mathbb{Z}/n)^2$, and in the index estimates for $\Gamma_H$ inside $\Gamma_1$ and in the orbit counts at full level; the proof cites [`ModularCurve.card_projectiveLine_zmod`](thm.html#ModularCurve.card_projectiveLine_zmod), the computation $\#\mathbb{P}^1(\mathbb{Z}/n) = \psi(n)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by sorry
