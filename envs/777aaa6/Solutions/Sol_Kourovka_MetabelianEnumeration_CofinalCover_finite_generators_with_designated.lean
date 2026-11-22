-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.finite_generators_with_designated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:48.68327+00:00
-- url     : https://prove2.me/submissions/9bfa041c-1ba5-4fc6-be5f-e29ced9b2f9f

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators

set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover ValuationModule
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {k : ℕ} {M : Type} [AddCommGroup M]
    [Module (GroupRing (Lattice k)) M] [Module.Finite (GroupRing (Lattice k)) M]
    (c : Fin k × Fin k → M) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ (A : Fin a → M) (designated : Fin k → Fin k → Fin a),
      Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤ ∧
      ∀ i j, A (designated i j) = c (i, j) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing (Lattice k)) (M := M)
  let d : Finset M := Finset.univ.image c
  let b : Finset M := insert 0 (s ∪ d)
  let e := Fintype.equivFin b
  let a := Fintype.card b
  let A : Fin a → M := fun i => (e.symm i).val
  have hbzero : (0 : M) ∈ b := Finset.mem_insert_self _ _
  have ha : 1 ≤ a := by
    letI : Nonempty b := ⟨⟨0, hbzero⟩⟩
    exact Fintype.card_pos_iff.mpr inferInstance
  have hc (i j : Fin k) : c (i, j) ∈ b :=
    Finset.mem_insert_of_mem (Finset.mem_union_right s
      (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  let designated : Fin k → Fin k → Fin a := fun i j => e ⟨c (i, j), hc i j⟩
  refine ⟨a, ha, A, designated, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    intro m hm
    have hmb : m ∈ b := Finset.mem_insert_of_mem (Finset.mem_union_left d hm)
    exact ⟨e ⟨m, hmb⟩, congrArg Subtype.val (e.symm_apply_apply ⟨m, hmb⟩)⟩
  · intro i j
    exact congrArg Subtype.val (e.symm_apply_apply ⟨c (i, j), hc i j⟩)
end Kourovka.MetabelianEnumeration.CofinalCover
