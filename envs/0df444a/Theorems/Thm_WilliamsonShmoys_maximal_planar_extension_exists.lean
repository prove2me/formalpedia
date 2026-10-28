-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists
-- name    : WilliamsonShmoys.maximal_planar_extension_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:48:44.338001+00:00
-- url     : https://prove2.me/theorems/2249af10-f397-4260-a2e1-3ef9a01c3c6b
-- title:
--   Every finite planar graph has a maximal planar extension
-- statement:
--   Any finite graph with the specified crossing-free drawing is a subgraph of a planar graph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) := by sorry
