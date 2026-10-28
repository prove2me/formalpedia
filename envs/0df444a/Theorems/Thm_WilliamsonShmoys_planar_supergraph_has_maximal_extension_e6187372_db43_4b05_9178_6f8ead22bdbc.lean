-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_has_maximal_extension_e6187372_db43_4b05_9178_6f8ead22bdbc
-- name    : WilliamsonShmoys.planar_supergraph_has_maximal_extension_e6187372_db43_4b05_9178_6f8ead22bdbc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:49:06.290327+00:00
-- url     : https://prove2.me/theorems/aba9a6ad-bad4-4d68-91de-03aab27830f2
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_has_maximal_extension_e6187372_db43_4b05_9178_6f8ead22bdbc
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
