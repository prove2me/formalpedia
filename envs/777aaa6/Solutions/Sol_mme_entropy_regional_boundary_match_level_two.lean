-- Prove2me | solution 1 for mme_entropy_regional_boundary_match_level_two
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T19:36:21.785653+00:00
-- url     : https://prove2.me/submissions/182ee69f-46c1-45f2-b243-24d83108669f

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_recursive_yz_cell_partition
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

set_option autoImplicit false

theorem solution
    (S : MME.RegionRealization.IntegerStep 2 2 (fun _ _ => True))
    (prof : MME.RecursiveYZ.Boundary.Profile 2 1)
    (hDim : prof.dim = 25)
    (halign : forall (i : Fin 3) (x : MME.ProfiledCW.FineWord 2),
      ((forall _p : Fin 1,
          MME.RecursiveYZ.CWCells.grade
            (@MME.ProfiledCW.split (Fin 1) 2 1 2 (Equiv.refl (Fin 1))
              (by decide : 1 * 2 ^ (2 - 1) = 2) x _p) =
            (prof.shape 0) i) /\
        MME.RecursiveYZ.Useful (fun _ : Fin 1 => (0 : Fin 1))
          (fun _ : Fin 1 => prof.mu 0 i)
          (@MME.ProfiledCW.split (Fin 1) 2 1 2 (Equiv.refl (Fin 1))
            (by decide : 1 * 2 ^ (2 - 1) = 2) x)) ->
      S.output i x) :
    exists (B : MME.ProfiledCW.BoundaryEnd 2 2 S.output),
      B.a * B.b * B.c = 25 /\ Nat.le 1 (B.a * B.b * B.c) := by
  have sub1 : forall a b : Fin 1, a = b := by decide
  have univ1 : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  have prod1 : forall f : Fin 1 -> Nat, (∏ j, f j) = f 0 := by
    intro f
    rw [univ1, Finset.prod_singleton]
  have fiber1 : forall j : Fin 1,
      Fin 1 ≃ {p : Fin 1 //
        (fun _ : Fin 1 => (0 : Fin 1)) p = Equiv.refl (Fin 1) j} := by
    intro j
    refine ⟨fun _ => ⟨0, sub1 _ _⟩, fun _ => 0,
      fun a => sub1 _ _, fun s => Subtype.ext (sub1 _ _)⟩
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
  refine ⟨⟨1, 1, rfl,
    (fun _ : Fin 1 => (0 : Fin 1)),
    (fun _ : Fin 1 => prof.shape 0),
    (fun (i : Fin 3) (_ : Fin 1) => prof.mu 0 i),
    ⟨1, Equiv.refl (Fin 1), fun _ => 1, fiber1⟩,
    (fun _ => prof), (fun _ => (0 : Fin 3)),
    (fun _ => rfl), (fun _ _ => rfl), halign⟩, ?_, ?_⟩
  · show (∏ _j : Fin 1, prof.a 0) * (∏ _j : Fin 1, prof.b 0) *
      (∏ _j : Fin 1, prof.c 0) = 25
    rw [ha, hb, hc, hDim]
  · show Nat.le 1 ((∏ _j : Fin 1, prof.a 0) * (∏ _j : Fin 1, prof.b 0) *
      (∏ _j : Fin 1, prof.c 0))
    rw [ha, hb, hc, hDim]
    norm_num
