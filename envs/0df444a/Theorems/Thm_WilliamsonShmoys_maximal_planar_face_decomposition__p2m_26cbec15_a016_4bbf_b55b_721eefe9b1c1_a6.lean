-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:35:22.106992+00:00
-- url     : https://prove2.me/theorems/dc18341a-a219-427c-98ac-62a72970a5ea
-- title:
--   Euler and triangular-face equations for maximal planar drawings
-- statement:
--   For a finite drawable graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, Set.Subset L.edgeSet M.edgeSet →
      HasPlanarDrawingOn M → Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
