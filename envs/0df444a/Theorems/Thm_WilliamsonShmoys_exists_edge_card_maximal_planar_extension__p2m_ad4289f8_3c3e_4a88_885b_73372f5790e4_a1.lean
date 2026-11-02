-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- name    : WilliamsonShmoys.exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:06.513649+00:00
-- url     : https://prove2.me/theorems/a87e4318-5b1f-4f35-a1db-9f570f1d2a03
-- title:
--   Maximum edge count among drawable extensions
-- statement:
--   Among the planar-drawable supergraphs of `H` on the same finite vertex type, there is one whose edge count is at least that of every other such extension. The family is nonempty since it contains `H`. Prove this by enumerating the finitely many simple graphs on `V`, restricting to extensions satisfying `HasPlanarDrawingOn`, and maximizing the natural-valued edge count. This removes the finite optimization step from the parent; the remaining parent argument applies the bound to any drawable graph above the selected `M`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      HasPlanarDrawingOn M ∧
      H.edgeFinset.card ≤ M.edgeFinset.card ∧
      ∀ N : SimpleGraph V, H ≤ N → HasPlanarDrawingOn N →
        N.edgeFinset.card ≤ M.edgeFinset.card := by sorry
