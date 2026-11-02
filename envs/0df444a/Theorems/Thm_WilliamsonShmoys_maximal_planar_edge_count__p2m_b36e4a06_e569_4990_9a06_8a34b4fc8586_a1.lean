-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:43.269193+00:00
-- url     : https://prove2.me/theorems/90a97550-9bbd-4224-be9a-687ae2f63607
-- title:
--   A maximal drawable graph has the planar edge count
-- statement:
--   An inclusion-maximal simple graph admitting the supplied crossing-free drawing on at least three vertices has exactly 3n−6 edges. The lower bound on the vertex count is needed for the planar triangulation edge formula and covers the three-vertex boundary case. Starting from the finite drawing, the independent proof route is to view its injective points and simple arcs as a finite plane embedding; maximality rules out disconnected components and faces with more than three sides, since an edge can be drawn through a face between suitable nonadjacent boundary vertices. Then Euler’s formula and counting each edge twice across face boundaries give 3n−6. Formalizing the correspondence between this predicate’s arc data and plane-embedding faces is the remaining core obligation; the supplied definition itself contains no Euler or face-counting theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ (M : SimpleGraph V), L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V)
    (hLdec : DecidableRel L.Adj) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
