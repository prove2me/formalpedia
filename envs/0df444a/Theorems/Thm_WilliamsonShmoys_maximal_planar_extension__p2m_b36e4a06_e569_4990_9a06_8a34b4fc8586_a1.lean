-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:45.48343+00:00
-- url     : https://prove2.me/theorems/30ecb5ea-f226-475a-a406-7f8a08cd96a3
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on the fixed finite vertex type is contained in an inclusion-maximal drawable graph. This uses only the finite choice among all simple graphs on the vertex type: choose a drawable supergraph with the greatest edge count. Any drawable supergraph of it must then have no additional edges. The child is independent of the target’s lower bound on the number of vertices. A proof can formalize the finite set of graphs, maximize edgeFinset.card, and use strict cardinal growth for a proper graph inclusion. It relies on the supplied drawing predicate being preserved as the same predicate on each candidate supergraph; it does not claim every supergraph is drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V), K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (M : SimpleGraph V), L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
