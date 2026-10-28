-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_connected_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:06:45.276963+00:00
-- url     : https://prove2.me/theorems/97829890-428d-4657-a899-f7e200a68a7c
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   A drawn finite graph with at least three vertices has a connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_connected_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
