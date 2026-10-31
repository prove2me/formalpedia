-- Prove2me | Theorems.Thm_finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- name    : finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:49.132101+00:00
-- url     : https://prove2.me/theorems/1a60f41f-9a39-459c-90ad-59757b78e94c
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   For a finite vertex type, the type of simple graphs on that vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
