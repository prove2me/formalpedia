-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:35.122539+00:00
-- url     : https://prove2.me/theorems/22b69642-7b63-43e8-8847-84301dc6da37
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite drawable graph on at least three vertices has a planar supergraph on the same vertices that is maximal among planar supergraphs under edge inclusion. This isolates the finite augmentation step from the edge-count argument. A proof route is to maximize the edge count over the finite set of planar supergraphs containing the original graph, then show any strict planar extension contradicts maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ (P : SimpleGraph V),
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
