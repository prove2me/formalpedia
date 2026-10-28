-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_2a77893c_8379_4827_8265_76a9c861f3f2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_2a77893c_8379_4827_8265_76a9c861f3f2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:33:14.068997+00:00
-- url     : https://prove2.me/theorems/e363935f-4247-44fb-9a3b-da8b387ef994
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every drawable graph L on finite V with at least three vertices is contained in a drawable supergraph that is maximal under inclusion among drawable graphs on V. The size hypothesis is retained for direct composition with the edge-count result, though finiteness alone suffices for this step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_2a77893c_8379_4827_8265_76a9c861f3f2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) := by sorry
