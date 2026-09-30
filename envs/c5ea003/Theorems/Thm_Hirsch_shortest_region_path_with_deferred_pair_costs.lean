-- Prove2me | Theorems.Thm_Hirsch_shortest_region_path_with_deferred_pair_costs
-- name    : Hirsch.shortest_region_path_with_deferred_pair_costs
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T15:58:32.374624+00:00
-- url     : https://prove2.me/theorems/ba2632b3-1bec-43f9-8755-960e4b04936c
-- title:
--   Shortest region paths with local costs supplied after portal selection
-- statement:
--   Let $(S_i)_{i\in I}$ be subsets of a set $V$, and let $G$ be a simple graph on $I$ such that adjacent labels have overlapping regions. Suppose $s$ and $t$ are connected in $G$, with $u\in S_s$ and $v\in S_t$.
--
--   There is a shortest, chordless region path $p$ from $s$ to $t$ and a list of portal pairs $(i,a_i,b_i)$ labelled, without repetition, by the support of $p$. Each pair lies in its labelled region. These choices can be made before choosing any routing graph $H$ on $V$ or nonnegative integer pair costs $C(i,a,b)$. For every such graph and cost assignment, if each listed pair admits an $H$-walk of length at most its assigned cost, then $u$ and $v$ admit an $H$-walk of length at most
--
--   $$\sum_{(i,a,b)\text{ in the chosen list}} C(i,a,b).$$
--
--   Only the selected portal pairs require local routes. The quantifier order permits local estimates to use the already chosen chordless support. This is an additive assembly theorem; it asserts no uniform polynomial bound for polytope diameters.
-- source:
--   https://github.com/jjoshua2/prove2me-work/blob/6db6759777606ad5c5243b716a4fe1ea59c80c8d/Solutions/PolynomialDeferredRegionCostsPublic.lean ; theorem Hirsch.shortest_region_path_with_deferred_pair_costs

import Mathlib

theorem Hirsch.shortest_region_path_with_deferred_pair_costs
    {V ι : Type*} (S : ι → Set V) (G : SimpleGraph ι)
    (hoverlap : ∀ i j, G.Adj i j → ∃ z, z ∈ S i ∧ z ∈ S j)
    {i j : ι} (hreach : G.Reachable i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : G.Walk i j,
      p.length = G.dist i j ∧ p.IsPath ∧
      (∀ r s : ℕ, r + 1 < s → s ≤ p.length →
        ¬ G.Adj (p.getVert r) (p.getVert s)) ∧
      ∃ legs : List (ι × V × V),
        legs.map Prod.fst = p.support ∧
        (legs.map Prod.fst).Nodup ∧
        (∀ leg ∈ legs, leg.2.1 ∈ S leg.1 ∧ leg.2.2 ∈ S leg.1) ∧
        ∀ (H : SimpleGraph V) (C : ι → V → V → ℕ),
          (∀ leg ∈ legs, ∃ q : H.Walk leg.2.1 leg.2.2,
            q.length ≤ C leg.1 leg.2.1 leg.2.2) →
          ∃ q : H.Walk u v,
            q.length ≤ (legs.map fun leg => C leg.1 leg.2.1 leg.2.2).sum := by sorry
