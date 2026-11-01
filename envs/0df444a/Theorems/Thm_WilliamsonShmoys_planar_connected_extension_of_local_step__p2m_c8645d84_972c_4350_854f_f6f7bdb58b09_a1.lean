-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- name    : WilliamsonShmoys.planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:12.098062+00:00
-- url     : https://prove2.me/theorems/fd72d2a3-1351-4a08-9062-0054809ba074
-- title:
--   Finite termination of planar component-joining steps
-- statement:
--   For a finite vertex type, if every disconnected planar supergraph of a drawn graph admits a planar supergraph adding an edge between previously unreachable vertices, then there is a connected planar supergraph of the original graph. The independent proof route is finite termination: each such edge merges at least two connected components, so only finitely many steps are possible.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
