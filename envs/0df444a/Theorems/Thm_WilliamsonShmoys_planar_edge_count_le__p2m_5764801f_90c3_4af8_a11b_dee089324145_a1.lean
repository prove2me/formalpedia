-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- name    : WilliamsonShmoys.planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:22.902742+00:00
-- url     : https://prove2.me/theorems/511609d8-7f6a-4ba7-bd36-d7671338159d
-- title:
--   Planar graphs obey the maximum edge bound
-- statement:
--   A graph with a planar drawing has at most `choose (card V) 2` edges below three vertices, and at most `3 * card V - 6` edges otherwise. A proof route uses the Euler formula for a plane embedding, with the small vertex counts handled directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeFinset.card ≤
      (if Fintype.card V < 3 then (Fintype.card V).choose 2
       else 3 * Fintype.card V - 6) := by sorry
