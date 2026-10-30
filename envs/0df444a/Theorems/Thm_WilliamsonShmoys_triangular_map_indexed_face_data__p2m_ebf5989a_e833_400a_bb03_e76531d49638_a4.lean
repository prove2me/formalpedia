-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- name    : WilliamsonShmoys.triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:04:42.525487+00:00
-- url     : https://prove2.me/theorems/3cab8724-95f9-4686-964b-b3385483fe12
-- title:
--   Reindex triangular map faces and transport indexed data
-- statement:
--   Reindex the faces of a triangular map by a finite ordinal, set each face length to three, and transport its dart equivalence, corner incidence, injectivity, vertex coverage, connectivity, and rotation transitivity. This packages the substantial structural construction for the parent. A proof route uses `Fintype.equivFin F` and transports the map fields, showing that modular successor on `Fin 3` agrees with the source successor and that the transported rotation iterates agree. The remaining core obligation is carrying out these equivalence and iterate transports in Lean. The length-three condition handles the modular denominator boundary, and `Nat.mod_lt` is justified by each input being a `Fin (length f)`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (F : Type) [Fintype F]
    (M : WilliamsonShmoys.TriangularMap H F) :
    ∃ (m : Nat) (length : Fin m → Nat)
      (corner : ∀ f, Fin (length f) → V)
      (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart),
      (∀ f, length f = 3) ∧
      (∀ f i, (dart ⟨f, i⟩).fst = corner f i) ∧
      (∀ f i, (dart ⟨f, i⟩).snd = corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      H.Connected ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart =>
            dart ⟨(dart.symm a.symm).1,
              ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
                Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e) := by sorry
