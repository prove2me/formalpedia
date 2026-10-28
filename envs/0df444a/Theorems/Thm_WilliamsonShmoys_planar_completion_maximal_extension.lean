-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_extension
-- name    : WilliamsonShmoys.planar_completion_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:59:55.253074+00:00
-- url     : https://prove2.me/theorems/e8d394e7-cd77-4c00-afb1-b037ff7b8b72
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every planar graph on a finite vertex type has a planar supergraph on the same vertices that is maximal under planar supergraph inclusion. The vertex-count hypothesis is retained to align the child with the target, though the finite-maximization argument does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V, HasPlanarDrawingOn M →
        (∀ u v, L.Adj u v → M.Adj u v) → M = L) := by sorry
