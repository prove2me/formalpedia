-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:33.943637+00:00
-- url     : https://prove2.me/theorems/0d7f4e6a-f018-419b-9ff8-3c6696d14d6d
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every finite drawable graph is contained in a drawable supergraph maximal under inclusion. The argument maximizes edge count among drawable supergraphs of M; a strict extension would increase that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    Exists (fun N : SimpleGraph V =>
      M <= N ∧ HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) := by
  sorry
