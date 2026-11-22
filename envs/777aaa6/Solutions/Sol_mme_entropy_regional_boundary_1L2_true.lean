-- Prove2me | solution 1 for mme_entropy_regional_boundary_1L2_true
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:17:22.654729+00:00
-- url     : https://prove2.me/submissions/fc0d8a4a-3f6d-4da2-96dc-f4b359ec2e61

import Theorems.Thm_mme_entropy_regional_profile_1L2_exists
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_compatibility
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

set_option autoImplicit false

theorem solution :
    exists (B : MME.ProfiledCW.BoundaryEnd 1 2 (fun _ _ => True)),
      B.a * B.b * B.c = 25 /\
      Nat.le 1 (B.a * B.b * B.c) := by
  have sub1 : forall a b : Fin 1, a = b := by decide
  have univ1 : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  have prod1 : forall f : Fin 1 -> Nat, (∏ j, f j) = f 0 := by
    intro f
    rw [univ1, Finset.prod_singleton]
  have fiber2 : forall j : Fin 1,
      Fin 2 ≃ {p : Fin 2 //
        (fun _ : Fin 2 => (0 : Fin 1)) p = Equiv.refl (Fin 1) j} := by
    intro j
    refine ⟨fun i => ⟨i, sub1 _ _⟩, fun s => s.val,
      fun _ => rfl, fun s => Subtype.ext rfl⟩
  obtain ⟨prof, hDim⟩ := mme_entropy_regional_profile_1L2_exists
  have ha : (∏ _j : Fin 1, prof.a 0) = 1 := by
    rw [prod1]
    show (if (0 : Fin 3) = 1 then prof.dim else 1) = 1
    rw [if_neg (by decide)]
  have hb : (∏ _j : Fin 1, prof.b 0) = 1 := by
    rw [prod1]
    show (if (0 : Fin 3) = 2 then prof.dim else 1) = 1
    rw [if_neg (by decide)]
  have hc : (∏ _j : Fin 1, prof.c 0) = prof.dim := by
    rw [prod1]
    show (if (0 : Fin 3) = 0 then prof.dim else 1) = prof.dim
    rw [if_pos rfl]
  refine ⟨⟨2, 1, (by decide : 2 * 2 ^ (1 - 1) = 2),
    (fun _ : Fin 2 => (0 : Fin 1)),
    (fun _ : Fin 1 => prof.shape 0),
    (fun (i : Fin 3) (_ : Fin 1) => prof.mu 0 i),
    ⟨1, Equiv.refl (Fin 1), fun _ => 2, fun j => fiber2 j⟩,
    (fun _ => prof), (fun _ => (0 : Fin 3)),
    (fun _ => rfl), (fun _ _ => rfl), (fun _ _ _ => trivial)⟩, ?_, ?_⟩
  · show (∏ _j : Fin 1, prof.a 0) * (∏ _j : Fin 1, prof.b 0) *
      (∏ _j : Fin 1, prof.c 0) = 25
    rw [ha, hb, hc, hDim]
  · show Nat.le 1 ((∏ _j : Fin 1, prof.a 0) * (∏ _j : Fin 1, prof.b 0) *
      (∏ _j : Fin 1, prof.c 0))
    rw [ha, hb, hc, hDim]
    norm_num
