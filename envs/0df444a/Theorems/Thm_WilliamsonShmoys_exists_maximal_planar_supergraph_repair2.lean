-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:34:02.028136+00:00
-- url     : https://prove2.me/theorems/83be3a68-1474-485f-8ac2-9f074f3ec101
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. The child reduces the target’s existential choice to a finite maximization argument; its proof can maximize edge count among all drawable supergraphs, a nonempty finite family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V, R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T →
        WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  sorry
