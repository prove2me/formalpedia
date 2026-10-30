-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_dense_planar_supergraph
-- name    : WilliamsonShmoys.exists_dense_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:00:20.550876+00:00
-- url     : https://prove2.me/theorems/f274a542-0cb7-49e3-9b4f-2bbc2d7007cc
-- title:
--   Completion to a maximally dense drawable supergraph
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_dense_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
