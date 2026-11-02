-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:11.546436+00:00
-- url     : https://prove2.me/theorems/724aac7b-31c9-4291-9b6d-4edefcb29b4d
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every connected finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn extends, on the same vertex set, to a graph with such a drawing and exactly 3|V|−6 edges. The extension contains every original edge. At |V|=3 the exact count is 3, as witnessed by K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ (H : SimpleGraph V), ∃ (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        (letI : DecidableRel H.Adj := dH
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  sorry
