-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_triangulation_extension_20261026
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_for_triangulation_extension_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:51:08.763695+00:00
-- url     : https://prove2.me/theorems/7b404d0f-df21-4652-ad3b-f2bfd20b64f3
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a supergraph on the same vertices that has a planar drawing and is maximal under graph inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_for_triangulation_extension_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
