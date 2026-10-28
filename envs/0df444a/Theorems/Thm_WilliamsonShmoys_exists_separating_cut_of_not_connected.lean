-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_separating_cut_of_not_connected
-- name    : WilliamsonShmoys.exists_separating_cut_of_not_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:08:11.133988+00:00
-- url     : https://prove2.me/theorems/56418066-6b4b-4674-b46c-36647e543c9b
-- title:
--   A disconnected graph has a nonempty edge-free cut
-- statement:
--   A finite disconnected graph on at least three vertices can be split into two nonempty sides with no edge crossing between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_separating_cut_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y := by sorry
