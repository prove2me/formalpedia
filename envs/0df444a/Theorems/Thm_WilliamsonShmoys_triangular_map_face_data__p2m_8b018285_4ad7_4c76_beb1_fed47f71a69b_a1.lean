-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
-- name    : WilliamsonShmoys.triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:29:38.466819+00:00
-- url     : https://prove2.me/theorems/ebf5989a-e833-400a-bb03-e76531d49638
-- title:
--   Convert a triangular map into indexed facial data
-- statement:
--   Given a triangular map and the target’s vertex and edge-count hypotheses, produce the exact indexed face, corner, dart, rotation, Euler, and total-corner data. The proof route reindexes the finite face type by `Fin m`, assigns length three to every face, transports the map’s dart equivalence and rotation, and derives the numerical equalities from the dart cardinality and `hcount`. The argument must account for Lean’s `Fin` successor and modular successor forms when transporting the corner-head and rotation fields.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (F : Type) [Fintype F]
    (M : WilliamsonShmoys.TriangularMap H F) :
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
