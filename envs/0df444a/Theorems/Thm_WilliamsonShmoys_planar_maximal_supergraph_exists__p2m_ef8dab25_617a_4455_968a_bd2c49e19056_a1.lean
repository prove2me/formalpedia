-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:05.430471+00:00
-- url     : https://prove2.me/theorems/8d3bb3a6-84b9-4586-bfa0-16ea8c3cae04
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      (∀ ⦃u v : V⦄, U.Adj u v → W.Adj u v) ∧
      HasPlanarDrawingOn W ∧
      (∀ N : SimpleGraph V, W ≤ N → HasPlanarDrawingOn N → N ≤ W) := by sorry
