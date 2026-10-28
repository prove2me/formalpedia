-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_c00979a8
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:50:56.171857+00:00
-- url     : https://prove2.me/theorems/e166d324-0b4e-4d08-b8f2-63eaa012950a
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Select an inclusion-maximal drawable supergraph of `N` from the finite family of drawable supergraphs on the same vertex type. The family is nonempty because it contains `N`; the vertex lower bound is not needed for this step. This removes the finite maximality argument from the parent. An independent proof route is to encode the candidate edge sets as a finite subtype, choose one with maximal edge-set cardinality, and show any proper supergraph has strictly more edges. The ordered type and drawing predicate remain exactly those of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 <= Fintype.card V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) : Exists fun K : SimpleGraph V => N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
