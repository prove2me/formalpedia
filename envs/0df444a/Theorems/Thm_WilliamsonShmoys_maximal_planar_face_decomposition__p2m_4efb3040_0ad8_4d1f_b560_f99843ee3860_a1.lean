-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:52.998367+00:00
-- url     : https://prove2.me/theorems/2e1bfcb4-daf5-4b6a-9257-36b9f3fd3710
-- title:
--   Euler and triangular-face equations for a maximal drawing
-- statement:
--   For a drawable graph on at least three vertices that is inclusion maximal among drawable supergraphs on the same vertex type, there is a natural face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hMax : ∀ N : SimpleGraph V, G ≤ N → HasPlanarDrawingOn N → N = G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f = 2 * G.edgeSet.ncard := by
  sorry
