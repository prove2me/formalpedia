-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:41.244044+00:00
-- url     : https://prove2.me/theorems/66972f67-2276-4586-a3cf-33d6080052b3
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
