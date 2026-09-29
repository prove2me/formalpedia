-- Prove2me | Theorems.Thm_MarkovMixing_rayleigh_monotonicity
-- name    : MarkovMixing.rayleigh_monotonicity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:00:38.275889+00:00
-- url     : https://prove2.me/theorems/2591393b-6c37-4874-b7a6-a78b7ddbe80e
-- title:
--   Theorem 9.12 -- Rayleigh's monotonicity law
-- statement:
--   Let $c$ and $c'$ be two **networks** on the same finite vertex set — symmetric nonnegative conductance functions, each with strictly positive total conductance $c(x)=\sum_yc(x,y)$ at every vertex and an irreducible associated walk $P(x,y)=c(x,y)/c(x)$. For distinct vertices $a\ne z$, the **effective resistance** $R_c(a\leftrightarrow z)$ is defined through the voltage $W(x)=\mathbb P_x\{\tau_a<\tau_z\}$ and the current $\|I\|=\sum_yc(a,y)[W(a)-W(y)]$ as $R_c(a\leftrightarrow z)=\|I\|^{-1}$.
--
--   The theorem (**Rayleigh's Monotonicity Law**, Theorem 9.12 of Levin–Peres–Wilmer) asserts: if $c'(x,y)\le c(x,y)$ on every edge — resistances are only increased — then
--   $$R_c(a\leftrightarrow z)\;\le\;R_{c'}(a\leftrightarrow z).$$
--   Decreasing conductances can only increase effective resistance. Deceptively simple, this is one of the most-used facts of the theory: it lets one bound resistances in a complicated network by deleting edges (setting conductances to zero) or by comparison with a tractable subnetwork, and through the commute-time identity it transfers to monotonicity statements for hitting times.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 9.4, Theorem 9.12, p. 123

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Theorem 9.12, Rayleigh's Monotonicity Law** (LPW): decreasing
conductances (increasing resistances) can only increase the effective
resistance: if `c' ≤ c` edgewise, then `R_c(a↔z) ≤ R_{c'}(a↔z)`. -/
theorem rayleigh_monotonicity {V : Type*} [Fintype V] [DecidableEq V]
    (c c' : V → V → ℝ) (hc : IsConductance c) (hc' : IsConductance c')
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hpos' : ∀ x : V, 0 < vertexConductance c' x)
    (hirr : Irreducible (networkWalk c)) (hirr' : Irreducible (networkWalk c'))
    (hle : ∀ x y : V, c' x y ≤ c x y) (a z : V) (haz : a ≠ z) :
    effectiveResistance c a z ≤ effectiveResistance c' a z := by
  sorry

end MarkovMixing
