-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augment_unreachable_pair_e285668e
-- name    : WilliamsonShmoys.planar_augment_unreachable_pair_e285668e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:10:18.837186+00:00
-- url     : https://prove2.me/theorems/d38312ce-717d-4a81-945b-d2e3deda09b0
-- title:
--   A planar drawing can be augmented across components
-- statement:
--   Given a crossing-free drawing and two distinct vertices in different connected components, there is a strict supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augment_unreachable_pair_e285668e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (u v : V)
    (huv : u ≠ v)
    (hUnreachable : ¬ L.Reachable u v) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
