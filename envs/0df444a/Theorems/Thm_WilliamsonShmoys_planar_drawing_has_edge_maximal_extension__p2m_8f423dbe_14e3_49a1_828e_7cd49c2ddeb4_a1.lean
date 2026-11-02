-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:20.701054+00:00
-- url     : https://prove2.me/theorems/f4b47241-0114-4ac8-84bb-0550b2f73838
-- title:
--   Extend a planar drawing to an inclusion-maximal planar supergraph
-- statement:
--   Every finite drawable graph on at least three vertices is contained in a drawable graph on the same vertices that has no strictly larger drawable simple supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
