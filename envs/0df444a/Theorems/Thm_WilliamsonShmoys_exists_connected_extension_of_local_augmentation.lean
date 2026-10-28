-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_extension_of_local_augmentation
-- name    : WilliamsonShmoys.exists_connected_extension_of_local_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:45:18.424993+00:00
-- url     : https://prove2.me/theorems/3ae5d68e-4b21-440e-baec-9e5af120bcce
-- title:
--   Finite maximality from local augmentation
-- statement:
--   For a finite vertex type, if every disconnected graph extending `X` that satisfies `P` can be strictly enlarged while preserving `P`, then some connected `P`-graph extends `X` and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_extension_of_local_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P X)
    (hAugment :
      ∀ G : SimpleGraph V, X ≤ G → P G → ¬ G.Connected →
        ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ Y : SimpleGraph V,
      X.edgeSet.ncard ≤ Y.edgeSet.ncard ∧ Y.Connected ∧ P Y := by
  sorry
