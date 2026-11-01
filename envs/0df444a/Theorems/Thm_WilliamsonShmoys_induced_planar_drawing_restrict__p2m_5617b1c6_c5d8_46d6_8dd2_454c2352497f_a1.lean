-- Prove2me | Theorems.Thm_WilliamsonShmoys_induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- name    : WilliamsonShmoys.induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:00.722201+00:00
-- url     : https://prove2.me/theorems/864764ff-9a27-4a11-9551-c80d7d547231
-- title:
--   Restriction of a planar drawing to an induced subgraph
-- statement:
--   Restrict any planar drawing of a finite ordered graph to the subtype of an arbitrary finset of vertices, including the empty finset. This removes the geometric inheritance step from the parent. Restrict the placement function and precompose each arc with the subtype coercions; the remaining core obligation is checking that the drawing predicates transport through these restrictions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hdraw : HasPlanarDrawingOn M) (C : Finset V) :
    HasPlanarDrawingOn (M.induce (C : Set V)) := by
  sorry
