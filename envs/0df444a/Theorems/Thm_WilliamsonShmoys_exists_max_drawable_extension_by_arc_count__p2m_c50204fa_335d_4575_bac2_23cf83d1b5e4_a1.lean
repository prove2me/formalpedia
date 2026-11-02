-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a1
-- name    : WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:29.703944+00:00
-- url     : https://prove2.me/theorems/b2c849ac-8790-42ab-867e-5ff846a44719
-- title:
--   Finite maximum among drawable supergraphs
-- statement:
--   Among all drawable supergraphs of a drawable finite graph, one maximizes the number of directed adjacent vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, N ≤ L → HasPlanarDrawingOn L →
          Nat.card {p : V × V // K.Adj p.1 p.2} ≤
            Nat.card {p : V × V // L.Adj p.1 p.2} := by sorry
