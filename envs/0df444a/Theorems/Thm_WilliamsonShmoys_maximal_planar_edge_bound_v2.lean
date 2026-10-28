-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:38:16.253082+00:00
-- url     : https://prove2.me/theorems/ed5aff95-88e9-44f9-b45f-1799d73180c2
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V| − 6 edges. The hypothesis |V| ≥ 3 is essential to the usual planar edge bound and is retained explicitly. A proof route is to use maximality to establish connectedness and triangular faces, then combine Euler's formula with the fact that each face has three boundary edges and each edge borders two faces. The case |V| = 3 yields the bound 3 directly. The substantial remaining work is proving these topological facts for the supplied continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
