-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal
-- name    : WilliamsonShmoys.planar_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:19:34.893886+00:00
-- url     : https://prove2.me/theorems/061e30bf-3e9a-4a8a-b1cc-6ee17117233d
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   A planar graph on a finite linearly ordered vertex type with at least three vertices has an edge-maximal planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_maximal {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn L ∧ K.edgeSet ⊆ L.edgeSet ∧ (∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M → L.edgeSet ⊆ M.edgeSet → M.edgeSet ⊆ L.edgeSet) := by sorry
