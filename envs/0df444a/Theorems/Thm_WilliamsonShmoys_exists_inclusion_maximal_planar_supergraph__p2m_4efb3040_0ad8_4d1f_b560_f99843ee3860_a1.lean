-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:47.294288+00:00
-- url     : https://prove2.me/theorems/cd8388a1-00a6-4989-92c9-fa93d023609b
-- title:
--   Existence of an inclusion maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is inclusion maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  sorry
