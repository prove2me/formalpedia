-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- name    : WilliamsonShmoys.planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:13.638594+00:00
-- url     : https://prove2.me/theorems/f40e01e7-1346-4075-bf35-9ce015d27098
-- title:
--   Local edge deficit for connected planar components
-- statement:
--   For each nonempty connected part, the edge count plus a size-dependent deficit is at most three times its vertex count. The deficit is 3 for singleton parts, 5 for size-two parts, and 6 for larger parts. For large parts this is exactly `hlarge`; for the two smaller cases, connectedness and simplicity bound their induced edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hconn : ∀ C, C ∈ parts → (M.induce (C : Set V)).Connected)
    (hdraw : ∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V)))
    (hlarge : ∀ C, C ∈ parts →
      3 ≤ Fintype.card {x : V // x ∈ C} →
      (M.induce (C : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {x : V // x ∈ C}) :
    ∀ C, C ∈ parts →
      (M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)
        ≤ 3 * Fintype.card {x : V // x ∈ C} := by sorry
