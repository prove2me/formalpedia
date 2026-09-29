-- Prove2me | Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo
-- name    : ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/cf26546a-64e3-5144-98b2-fa8067c608c0
-- title:
--   Counting τ-stable cyclic subgroups of order n in (ℤ/n)²
-- statement:
--   Let $n$ be a natural number with $n \neq 0$, and let $\tau \colon \mathbb{Z}/n \times \mathbb{Z}/n \to \mathbb{Z}/n \times \mathbb{Z}/n$ be an endomorphism of the underlying additive group, subject to two hypotheses: first, $\tau(\tau(v)) = -v$ for every $v$, so that $\tau^2 = -1$; second, for every prime $p$ dividing $n$ there is an element $v$ of $\mathbb{Z}/n \times \mathbb{Z}/n$ of additive order exactly $p$ such that $\tau(v) \neq k \cdot v$ for every natural number $k$, i.e. $\tau$ is nowhere scalar on $p$-torsion in this sense. The conclusion is an equality of cardinalities: the number of additive subgroups $H \le \mathbb{Z}/n \times \mathbb{Z}/n$ which are cyclic, have cardinality exactly $n$, and satisfy $\tau(H) = H$ (the image of $H$ under $\tau$ being equal to $H$) equals $\nu_2(n)$, which by definition is the number of $x \in \mathbb{Z}/n$ with $x^2 + 1 = 0$.
--
--   This is the arithmetic core of the count of elliptic points of order two (the points above $j = 1728$) on the modular curve $Y_0(N)$: cyclic subgroups of order $N$ in $E[N] \cong (\mathbb{Z}/N)^2$ stable under an automorphism of order four correspond to square roots of $-1$ modulo $N$. It is used to transport the count to an abstract abelian group with $N$-torsion $(\mathbb{Z}/N)^2$, and thence to the computation of the relevant orbit counts for $\Gamma_0(N)$ acting with the elements $S$ and $ST$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) = -v)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuTwo n := by sorry
