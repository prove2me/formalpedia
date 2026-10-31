-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:24.036487+00:00
-- url     : https://prove2.me/theorems/444cd434-7013-46bb-9e82-d756827f6b0e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-maximal drawable simple graph with at least three vertices has exactly 3|V| − 6 edges. The standard proof route establishes connectivity and triangular faces from maximality, then applies Euler’s formula and counts edge-face incidences; the three-vertex case is the triangle. This removes the entire edge-count theorem from the parent. The remaining core is formalizing the face structure and Euler counting for the given arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L.edgeFinset = K.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
