-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_card__p2m_d9ec561c_5413_404b_9cc9_bfd18ae2ee8f_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_card__p2m_d9ec561c_5413_404b_9cc9_bfd18ae2ee8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:27.954568+00:00
-- url     : https://prove2.me/theorems/7d763046-bd9d-4f1f-91cd-beb84c124b85
-- title:
--   Planar drawing extension to a triangulation
-- statement:
--   Every connected drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_card__p2m_d9ec561c_5413_404b_9cc9_bfd18ae2ee8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) (hconn : N.Connected) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj
       3 * Fintype.card V - 6 = P.edgeFinset.card) := by sorry
