-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:08:34.275123+00:00
-- url     : https://prove2.me/theorems/4b285708-9045-4545-bfe4-7efc662502bd
-- title:
--   Existence of a maximal drawn supergraph (job-specific declaration)
-- statement:
--   Every finite drawn simple graph is contained in a drawn supergraph that has no strictly larger drawn supergraph on the same vertex set. The finiteness of the set of simple graphs permits maximizing the number of edges among eligible supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N := by
  sorry
