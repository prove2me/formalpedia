-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:07:05.119772+00:00
-- url     : https://prove2.me/theorems/e32bb1c8-42c6-4cbd-80a5-f05346e950c3
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph on the same vertex type. Among the finitely many simple graphs containing K, choose a drawable one with the largest edge count. A drawable proper supergraph would have more edges, contradicting maximality of that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧ K ≤ L ∧
      ∀ M : SimpleGraph V, HasPlanarDrawingOn M → L ≤ M → M = L := by
  sorry
