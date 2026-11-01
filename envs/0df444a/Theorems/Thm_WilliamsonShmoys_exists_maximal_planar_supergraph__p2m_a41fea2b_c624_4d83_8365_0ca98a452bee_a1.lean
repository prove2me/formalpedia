-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:32.599125+00:00
-- url     : https://prove2.me/theorems/5ad4dfa2-7b03-4649-bf47-2550ad7ee6b8
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ {u v : V}, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ Q : SimpleGraph V,
        (∀ {u v : V}, P.Adj u v → Q.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        (∀ {u v : V}, Q.Adj u v → P.Adj u v)) := by sorry
