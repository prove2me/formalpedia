-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T07:59:40.078983+00:00
-- url     : https://prove2.me/theorems/0550ae95-7628-4ffc-a23b-1a34e7221b20
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   If a drawable graph is edge-count-maximal among drawable supergraphs of a fixed drawable subgraph, and there are at least three vertices, then it has exactly 3|V| − 6 edges. Any drawable supergraph of this maximal graph is also a candidate supergraph of the fixed graph, so maximality prevents adding an edge. The remaining proof establishes that such a maximal planar drawing has triangular faces and applies Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hMN : M ≤ N)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      N.edgeSet.ncard ≤ K.edgeSet.ncard) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
