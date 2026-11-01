-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a1
-- name    : WilliamsonShmoys.exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:32.457765+00:00
-- url     : https://prove2.me/theorems/43e6dd0c-2004-4107-850e-c98c33b7b33a
-- title:
--   Every finite planar drawing has a triangulated supergraph
-- statement:
--   Any crossing-free drawing on a finite vertex set of size at least three extends, on the same vertex set, to a drawable graph with exactly three times the vertex count minus six edges. For three vertices the extension is the triangle; for larger sets it is obtained by completing the planar regions to triangular faces. The parent theorem follows because its maximality hypothesis forces this supergraph to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ hKdec : DecidableRel K.Adj,
        K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
