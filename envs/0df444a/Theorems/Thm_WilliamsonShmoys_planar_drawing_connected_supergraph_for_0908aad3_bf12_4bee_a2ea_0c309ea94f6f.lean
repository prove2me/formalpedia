-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:41:04.519419+00:00
-- url     : https://prove2.me/theorems/72364670-a46d-435b-9cd5-0d241b47404b
-- title:
--   Connect a drawable graph by adding edges
-- statement:
--   Every nonempty finite drawable simple graph has a connected drawable supergraph on the same vertices. It supplies the connected graph needed for the edge-count step while preserving edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
