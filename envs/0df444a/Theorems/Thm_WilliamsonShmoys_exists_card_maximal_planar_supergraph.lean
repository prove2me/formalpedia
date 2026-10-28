-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_card_maximal_planar_supergraph
-- name    : WilliamsonShmoys.exists_card_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:50:48.293315+00:00
-- url     : https://prove2.me/theorems/e36d0be4-c353-49ae-85a7-75c9ebaf463b
-- title:
--   A drawable graph has a drawable supergraph of maximum edge count
-- statement:
--   Among the drawable supergraphs of K on the same finite vertex set, one has maximum edge count. There are finitely many simple graphs on that vertex set, and K itself is an eligible supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_card_maximal_planar_supergraph {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
