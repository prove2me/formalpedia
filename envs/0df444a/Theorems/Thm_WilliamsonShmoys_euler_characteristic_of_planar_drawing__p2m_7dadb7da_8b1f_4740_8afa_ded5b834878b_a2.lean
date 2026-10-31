-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- name    : WilliamsonShmoys.euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:26.359258+00:00
-- url     : https://prove2.me/theorems/b2c4c164-034f-445b-b0e5-31939db5e70c
-- title:
--   Euler characteristic for a connected planar drawing
-- statement:
--   For a finite connected graph with the given crossing-free drawing, there is a natural-number face count satisfying Euler’s equation. Connectedness is needed for the single-component Euler formula; the claim also covers the small connected cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : Exists fun F : Nat => Fintype.card V + F = G.edgeSet.ncard + 2 := by sorry
