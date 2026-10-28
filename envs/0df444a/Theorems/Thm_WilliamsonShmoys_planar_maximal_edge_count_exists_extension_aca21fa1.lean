-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_exists_extension_aca21fa1
-- name    : WilliamsonShmoys.planar_maximal_edge_count_exists_extension_aca21fa1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:48:45.456628+00:00
-- url     : https://prove2.me/theorems/8ac17300-7c56-4ce4-b3be-f46b436ebf4c
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under drawable edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count_exists_extension_aca21fa1
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y) :
    Exists (fun Z : SimpleGraph V =>
      And (HasPlanarDrawingOn Z)
        (And ((u v : V) -> Y.Adj u v -> Z.Adj u v)
          ((W : SimpleGraph V) -> HasPlanarDrawingOn W ->
            ((u v : V) -> Z.Adj u v -> W.Adj u v) ->
            (u v : V) -> W.Adj u v -> Z.Adj u v))) := by sorry
