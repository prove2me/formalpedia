-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
-- name    : WilliamsonShmoys.local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:08.069654+00:00
-- url     : https://prove2.me/theorems/60d14aea-be69-4b51-a6fb-6f45c6ceb723
-- title:
--   A local rotation gap permits a planar extension
-- statement:
--   For a drawable graph with the stated triangular dart data, if two darts at the same vertex are not connected by iterating the induced successor, there is a strict planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.local_rotation_gap_yields_planar_extension__p2m_e63143a4_1d37_4669_84fc_4ce72e6e836f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (d e : H.Dart)
    (hde : d.fst = e.fst)
    (hgap :
      ¬ ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by sorry
