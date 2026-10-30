-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:06:46.261347+00:00
-- url     : https://prove2.me/theorems/8b018285-4ad7-4c76-beb1-fed47f71a69b
-- title:
--   Extract finite facial-walk data from a maximal planar drawing
-- statement:
--   Extract finite facial walks, corner vertices, oriented darts, vertex coverage, rotation data, Euler’s equation, and the total corner count from the planar drawing. The modular-successor bounds use the relevant `Fin` indices’ own bounds. This child separates the topological construction from the parent. A proof route is to derive cyclic orders from the drawing, form facial walks, and prove their incidence and counting properties. The remaining core obligation is formalizing this extraction from `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ (m : Nat) (length : Fin m → Nat)
      (corner : ∀ f, Fin (length f) → V)
      (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart),
      (∀ f i, (dart ⟨f, i⟩).fst = corner f i) ∧
      (∀ f i, (dart ⟨f, i⟩).snd = corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      H.Connected ∧
      (∀ f, 3 ≤ length f) ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart =>
            dart ⟨(dart.symm a.symm).1,
              ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
                Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e) ∧
      m + Fintype.card V = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard := by sorry
