-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_of_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- name    : WilliamsonShmoys.triangular_map_of_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:06:49.490535+00:00
-- url     : https://prove2.me/theorems/dd23d678-8eab-4ad2-a2ed-b1e85db421a2
-- title:
--   Convert maximal facial-walk data into a triangular map
-- statement:
--   Use the face data, Euler equation, edge count, and corner count to show every face has length three, then reindex each face’s corners to construct a `TriangularMap`. This removes the finite counting and dependent reindexing work from the parent. A proof route is to derive `3*m = 2*H.edgeSet.ncard` arithmetically, compare the sum of face lengths against the lower bound of three per face, and transport the dart, incidence, coverage, and rotation fields along the resulting length equalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.triangular_map_of_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (m : Nat)
    (length : Fin m → Nat)
    (corner : ∀ f, Fin (length f) → V)
    (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart)
    (htail : ∀ f i, (dart ⟨f, i⟩).fst = corner f i)
    (hhead : ∀ f i, (dart ⟨f, i⟩).snd = corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)
    (hdistinct : ∀ f, Function.Injective (corner f))
    (hcovered : ∀ v, ∃ f i, corner f i = v)
    (hconnected : H.Connected)
    (hlen : ∀ f, 3 ≤ length f)
    (hrotation : ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ⟨(dart.symm a.symm).1,
            ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
              Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e)
    (heuler : m + Fintype.card V = H.edgeSet.ncard + 2)
    (hcorners : (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ n : Nat, Nonempty (WilliamsonShmoys.TriangularMap H (Fin n)) := by sorry
