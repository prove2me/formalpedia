-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:27.370985+00:00
-- url     : https://prove2.me/theorems/e39dc392-ef53-43de-92b9-a9ba96581299
-- title:
--   Every planar graph has an edge-maximal planar completion
-- statement:
--   Any graph with the specified planar drawing has an edge-inclusion-maximal planar supergraph on the same finite vertex type. Finiteness gives a maximal choice among the planar supergraphs containing the original graph; the drawing is preserved when edges are removed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
