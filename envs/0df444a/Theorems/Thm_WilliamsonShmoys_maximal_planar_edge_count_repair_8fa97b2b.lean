-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_8fa97b2b
-- name    : WilliamsonShmoys.maximal_planar_edge_count_repair_8fa97b2b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:51:51.821876+00:00
-- url     : https://prove2.me/theorems/d150337f-4da9-4e19-abdf-d7ebc4ba6ea5
-- title:
--   Euler edge bound for a maximal planar drawing
-- statement:
--   A finite simple graph on at least three vertices whose planar drawing admits no proper planar edge-set extension has at most 3|V|−6 edges. The proof must derive the needed connectivity and face-count consequences of maximality, then use Euler’s formula and the fact that each face has degree at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_repair_8fa97b2b
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
