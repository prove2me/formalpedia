-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:36:01.678508+00:00
-- url     : https://prove2.me/theorems/e5aec6ab-a82c-433f-9c0e-062437eec0e4
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   A finite drawable graph has a drawable supergraph on the same vertices that is maximal under graph inclusion. The vertex-count hypothesis is retained to match the parent, though the finite maximization argument does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, G ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L := by sorry
