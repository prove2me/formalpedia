-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:54:05.486033+00:00
-- url     : https://prove2.me/theorems/2f86201a-e66d-4d67-a95b-7a1796c4df66
-- title:
--   Maximal planar extension on the same vertices
-- statement:
--   Every graph with the specified planar drawing has a drawable supergraph on the same finite vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, M.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ R : SimpleGraph V,
        (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) := by sorry
