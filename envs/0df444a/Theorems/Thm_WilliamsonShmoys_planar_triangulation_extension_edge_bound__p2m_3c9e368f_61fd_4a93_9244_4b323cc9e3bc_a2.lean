-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:12.382596+00:00
-- url     : https://prove2.me/theorems/74da5e6a-674d-4f79-986e-ea1a1f3184a0
-- title:
--   Planar triangulation extension edge bound
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices is contained in a drawable simple graph on the same vertices whose edge count is at least 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V =>
      (forall {u v : V}, L.Adj u v -> M.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       3 * Fintype.card V - 6 <= M.edgeFinset.card) := by sorry
