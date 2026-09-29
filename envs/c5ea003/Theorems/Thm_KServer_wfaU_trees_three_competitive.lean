-- Prove2me | Theorems.Thm_KServer_wfaU_trees_three_competitive
-- name    : KServer.wfaU_trees_three_competitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T03:58:41.29637+00:00
-- url     : https://prove2.me/theorems/06e65a50-3c45-42a7-9a73-a14c1cd94ccb
-- title:
--   CK 2021, Theorem 23 — WFA is $3$-competitive for $3$ servers on trees
-- statement:
--   **Theorem 23 of Coester and Koutsoupias.** The Work Function Algorithm is $3$-competitive for $3$ servers on trees.
--
--   Let $M$ be the vertex set of a finite weighted tree, carrying the path metric, and let $C_0$ be an initial configuration of three servers. Then there is a constant $a$, depending on the space and on $C_0$ but not on the request sequence, with
--
--   $$\mathrm{cost}(\mathrm{WFA}, \sigma) \;\le\; 3 \cdot \mathrm{OPT}(\sigma) + a \qquad \text{for every } \sigma.$$
--
--   Since $k$-competitiveness is conjectured to be optimal and is known to be a lower bound for every deterministic algorithm on any metric space with more than $k$ points, this is a tight bound for $k = 3$: it settles the $k$-server conjecture for three servers on trees.
--
--   ## Context
--
--   The general upper bound for the Work Function Algorithm is $2k-1$, which gives $5$ for three servers. Bringing it down to $k$ has been achieved only on restricted spaces --- the line, spaces of $k+1$ and $k+2$ points, the Manhattan plane for $k=3$ --- and trees for $k=3$ is the case Coester and Koutsoupias settle, by exhibiting a potential function satisfying an *offset* and an *update* property, the latter proved using the fact that a metric is a tree metric exactly when it is quasiconcave.
--
--   ## What `WFA` means here
--
--   The algorithm is the classical one: after each request it moves to a configuration containing the request minimising movement cost plus the work function of the **unlabelled** configuration --- the work function whose final move is a minimum-cost matching, which is the one all of the classical theory concerns.
--
--   The distinction matters. A configuration is formally a function $\{1,2,3\} \to M$, and one can build a work function that demands server $i$ finish at a *named* point; the resulting algorithm is a different one, and it is not $3$-competitive on trees. On the path $0 - 1 - 2 - 3$ with edge weights $2, 4, 4$ and initial configuration $(1,0,3)$ there is an admissible run of that variant which is eventually periodic with period $7$, of cost $28$ per period against an optimal offline cost of $8$, so its ratio tends to $7/2$ and no additive constant suffices. The loss is a step whose labelled cost is $8$ while the matching between the same two point sets costs $4$: two servers exchange positions and buy nothing. Minimising against the unlabelled work function removes exactly this, because the work function is then blind to the labelling while the movement cost is not, so the minimisation itself selects the matching.
--
--   ## Formalization note
--
--   `IsTreeVertexSpace M` says the metric on $M$ is the path metric of a weighted tree whose vertex set is $M$ itself. `WFAU` is the classical Work Function Algorithm as above; ties in its step are broken by a fixed arbitrary choice, and the statement is asserted for that algorithm however they are broken. `IsCompetitive A c` is the usual $\exists a, \forall \sigma,\ \mathrm{cost} \le c \cdot \mathrm{OPT} + a$, with $\mathrm{OPT}$ the optimal offline cost from $A$'s initial configuration.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section on trees, Theorem 23: 'WFA is 3-competitive for 3 servers on trees.'

import Mathlib
import Definitions.Def_KServer_wfaU
import Definitions.Def_KServer_tree_metric

namespace KServer

theorem wfaU_trees_three_competitive {M : Type*} [MetricSpace M] [Fintype M]
    (hM : IsTreeVertexSpace M) (C₀ : Config 3 M) :
    IsCompetitive (WFAU (Nat.succ_pos 2) C₀) 3 := by sorry

end KServer
