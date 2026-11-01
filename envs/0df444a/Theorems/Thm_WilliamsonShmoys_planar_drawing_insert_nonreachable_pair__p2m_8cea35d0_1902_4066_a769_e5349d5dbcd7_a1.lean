-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
-- name    : WilliamsonShmoys.planar_drawing_insert_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:44.851705+00:00
-- url     : https://prove2.me/theorems/977349e9-5ccc-4485-876d-167ab0b783a0
-- title:
--   Extend a planar drawing across a non-reachable pair
-- statement:
--   For any pair of vertices in different connected components of a graph with a planar drawing, there is a strict planar supergraph on the same vertex type. This isolates the edge-insertion geometry from selecting the pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_insert_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∀ u v : V, ¬ H.Reachable u v →
      ∃ H' : SimpleGraph V, H < H' ∧ HasPlanarDrawingOn H' := by sorry
