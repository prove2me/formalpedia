-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_on_card_edge_count
-- name    : WilliamsonShmoys.maximal_planar_on_card_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:56:27.496406+00:00
-- url     : https://prove2.me/theorems/0f19bc82-998b-4432-b1c2-bf0c9fdc5c2a
-- title:
--   An inclusion-maximal planar graph has the Euler edge count
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_on_card_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKmax : IsMaximalPlanarOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
