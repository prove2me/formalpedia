-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_family
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_family
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:16:12.721984+00:00
-- url     : https://prove2.me/theorems/58296d12-4643-4193-9dc9-f7d8810df6bd
-- title:
--   Maximal member of a family of finite simple graphs
-- statement:
--   Every nonempty proposition-defined family of simple graphs on a finite vertex type has a member with no strictly larger member in that family. No decidability assumption on the family predicate is needed. The edge-count maximization proof also covers the empty vertex type: its only graph has edge count zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_simpleGraph_family
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ G : SimpleGraph V, P G ∧
      ∀ L : SimpleGraph V, P L → G ≤ L → L = G := by sorry
