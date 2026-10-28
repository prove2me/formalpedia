-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_extension_reaches_connected
-- name    : WilliamsonShmoys.finite_extension_reaches_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:16:59.983567+00:00
-- url     : https://prove2.me/theorems/269d2b8e-9e77-4ead-8706-3fa6d53fa238
-- title:
--   A finite drawable-extension process reaches connectedness
-- statement:
--   If a property of finite simple graphs is preserved along strict extensions, and every disconnected extension with that property has a further strict extension with the property, then there is a connected extension with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_extension_reaches_connected
    {V : Type} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hstep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ K : SimpleGraph V, W ≤ K ∧ K.Connected ∧ P K := by sorry
