-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:03.661373+00:00
-- url     : https://prove2.me/theorems/8d0b95f1-3d22-423b-9850-63148fea79a7
-- title:
--   Triangulating a drawable graph on the same vertices
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices and a drawing satisfying HasPlanarDrawingOn is contained in a graph on the same vertex type that also satisfies HasPlanarDrawingOn and has exactly 3|V|−6 edges. This is the standard planar triangulation-extension result, specialized to the supplied drawing predicate; its proof must preserve all vertices and the precise crossing-free arc conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
