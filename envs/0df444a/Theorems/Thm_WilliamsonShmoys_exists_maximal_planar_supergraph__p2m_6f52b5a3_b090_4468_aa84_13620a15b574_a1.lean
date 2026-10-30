-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:33:18.722632+00:00
-- url     : https://prove2.me/theorems/469d9da7-7454-4371-9a4f-4cc419f09ed2
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. The route is finite maximization: among the finitely many edge sets containing M that admit a drawing, choose one of largest cardinality. This removes the existence and maximality choice from the parent. The relevant argument is that the class being maximized is nonempty (it contains M), and inclusion plus equal finite edge counts implies graph equality. No lower bound on |V| is needed for this child. The remaining core obligation is making the finite maximization argument work with the existential drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
