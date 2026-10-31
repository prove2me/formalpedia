-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:48.756315+00:00
-- url     : https://prove2.me/theorems/3a18cd50-a833-4853-9055-3e93726fc3e4
-- title:
--   Extension of a planar graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. The extension is obtained by triangulating a maximal drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
