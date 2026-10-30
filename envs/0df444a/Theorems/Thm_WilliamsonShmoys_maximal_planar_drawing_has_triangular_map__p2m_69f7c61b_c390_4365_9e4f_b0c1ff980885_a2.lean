-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_map__p2m_69f7c61b_c390_4365_9e4f_b0c1ff980885_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_69f7c61b_c390_4365_9e4f_b0c1ff980885_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:09.084716+00:00
-- url     : https://prove2.me/theorems/3a63b1c2-5291-4a00-a57c-55b53f8ceff2
-- title:
--   A maximal planar drawing yields a connected triangular map
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same finite vertex set, with at least three vertices, admits a finite triangular map. The map accounts for every oriented edge exactly once, has distinct corners on each face, covers every vertex, and also has a connected primal graph and transitive vertex rotations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_69f7c61b_c390_4365_9e4f_b0c1ff980885_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F),
      Nonempty (@WilliamsonShmoys.TriangularMap V ‹Fintype V› H F instF) := by sorry
