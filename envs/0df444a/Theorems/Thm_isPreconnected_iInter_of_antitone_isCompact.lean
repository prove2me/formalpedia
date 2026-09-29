-- Prove2me | Theorems.Thm_isPreconnected_iInter_of_antitone_isCompact
-- name    : isPreconnected_iInter_of_antitone_isCompact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T21:44:05.928485+00:00
-- url     : https://prove2.me/theorems/9fecd9d4-da3a-4839-82e5-32abd22dc1ab
-- title:
--   Cantor intersection theorem for connectedness: a nested intersection of compact connected sets is connected
-- statement:
--   Let $X$ be a Hausdorff topological space and let
--
--   $$K_0 \supseteq K_1 \supseteq K_2 \supseteq \cdots$$
--
--   be a decreasing sequence of compact, connected (more precisely: preconnected) subsets of $X$. Then the intersection
--
--   $$K \;=\; \bigcap_{n \in \mathbb{N}} K_n$$
--
--   is again preconnected.
--
--   This is the connectedness companion of Cantor's intersection theorem (which asserts that $K$ is nonempty when every $K_n$ is). Compactness is essential: in the plane the decreasing sequence of closed connected sets $\{(x,y) : x \ge n\}$ has empty — hence connected — intersection, but replacing "compact" by "closed" in general fails, the standard counterexample being a decreasing sequence of closed connected subsets of the plane whose intersection is a pair of disjoint horizontal rays.
--
--   The proof is the standard separation argument: if $K = A \sqcup B$ with $A, B$ disjoint, closed and nonempty, then $A$ and $B$ are disjoint compact sets, so by the Hausdorff property they can be surrounded by disjoint open sets $U \supseteq A$ and $V \supseteq B$. The compact sets $K_n \setminus (U \cup V)$ decrease and have empty intersection, so one of them is empty; that $K_n$ is then split by $U$ and $V$ into two nonempty relatively open pieces, contradicting its connectedness.
--
--   Preconnectedness (rather than connectedness) is the right formulation because the intersection may be empty.
-- source:
--   Standard point-set topology; see e.g. S. Willard, General Topology, Addison-Wesley 1970, Theorem 28.2 (the intersection of a nested family of compact connected sets in a Hausdorff space is connected).

import Mathlib
open Set Topology

theorem isPreconnected_iInter_of_antitone_isCompact
    {α : Type*} [TopologicalSpace α] [T2Space α] {s : ℕ → Set α}
    (hanti : Antitone s) (hcomp : ∀ n, IsCompact (s n))
    (hconn : ∀ n, IsPreconnected (s n)) :
    IsPreconnected (⋂ n, s n) := by sorry
