-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:14.599707+00:00
-- url     : https://prove2.me/theorems/0fcc7dbf-d44c-4c92-a564-56b4ef76a7fc
-- title:
--   Every drawn finite graph has a maximal drawn supergraph
-- statement:
--   On a fixed finite vertex type, every graph admitting the specified drawing is contained in an inclusion-maximal graph that also admits such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ M' : SimpleGraph V, HasPlanarDrawingOn M' ∧ M ≤ M' ∧
      ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M' ≤ N → N = M' := by sorry
