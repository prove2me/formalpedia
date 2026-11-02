-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:56.843145+00:00
-- url     : https://prove2.me/theorems/3b9c1b25-36f2-49fb-9760-e5ee7be0caf4
-- title:
--   Connect components of a finite planar drawing by adding edges
-- statement:
--   Extend any finite planar drawing on the same vertex set to a connected planar drawing, retaining every original edge. The classical adjacency decision procedure is installed in the statement before using `edgeFinset`. For the proof, connect distinct drawn components by adding an arc in a face incident to them, repeating until connected; finiteness makes the process terminate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      J.edgeFinset ⊆ H.edgeFinset := by sorry
