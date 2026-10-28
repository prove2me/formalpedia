-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:25:06.241072+00:00
-- url     : https://prove2.me/theorems/1cbcc25f-b5ec-4698-b79f-1253b09f71e3
-- title:
--   Finite maximal supergraph for a hereditary property
-- statement:
--   On a finite vertex type, any graph satisfying a property that is preserved by taking subgraphs has a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_property
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  sorry
