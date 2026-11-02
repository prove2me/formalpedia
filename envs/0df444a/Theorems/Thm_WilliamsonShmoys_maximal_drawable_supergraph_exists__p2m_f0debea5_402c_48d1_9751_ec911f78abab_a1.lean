-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:25.852264+00:00
-- url     : https://prove2.me/theorems/bc74717e-1fc9-449c-b8e0-920a52161d50
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, ∃ (hNdec : DecidableRel N.Adj), M ≤ N ∧ HasPlanarDrawingOn N ∧ (∀ (P : SimpleGraph V) [DecidableRel P.Adj], N ≤ P → HasPlanarDrawingOn P → P = N) := by sorry
