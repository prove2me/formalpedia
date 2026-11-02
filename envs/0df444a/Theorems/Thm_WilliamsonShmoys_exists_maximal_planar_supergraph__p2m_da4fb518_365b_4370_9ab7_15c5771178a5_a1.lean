-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:09.570207+00:00
-- url     : https://prove2.me/theorems/59d8957b-0c70-43c1-9102-641dd15e2913
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every finite connected drawable graph with at least three vertices is contained in a drawable graph on the same vertex set that is maximal under graph inclusion. This removes the task of handling arbitrary drawings from the edge-counting step. Since there are only finitely many simple graphs on the fixed finite vertex set, choose a drawable supergraph with the largest edge count; any drawable strict supergraph would have strictly more edges. The connectedness hypothesis is inherited by the extension and is retained for the next child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
