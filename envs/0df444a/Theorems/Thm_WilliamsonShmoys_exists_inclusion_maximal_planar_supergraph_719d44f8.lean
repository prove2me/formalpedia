-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_719d44f8
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_719d44f8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:06:23.511088+00:00
-- url     : https://prove2.me/theorems/14277f5b-bfc5-4623-a848-2ac6abb3000c
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   On the fixed finite vertex set, extend any drawable graph to one maximal under inclusion among drawable graphs. The proof route is finite maximality: consider the finite collection of simple graphs on V that contain H and satisfy the drawing predicate, then choose an inclusion-maximal member. This removes the extension step from the parent; the drawing predicate need not be decidable because maximality is taken over a finite, nonempty proposition-defined collection.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_719d44f8
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
