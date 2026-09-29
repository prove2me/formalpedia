-- Prove2me | solution 1 for mme_prescribed_cell_query_permutation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:26:39.368448+00:00
-- url     : https://prove2.me/submissions/7d081f00-a31c-4dfe-bcaf-f6f65278f2f1

import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option maxHeartbeats 600000

theorem solution {P C J : Type*} [Fintype P] [Fintype J]
    (cell : P → C) (q u : J → P) (hq : Function.Injective q)
    (hu : Function.Injective u) (hc : ∀ j, cell (q j) = cell (u j)) :
    ∃ e : Equiv.Perm P, (∀ p, cell (e p) = cell p) ∧ ∀ j, e (q j) = u j := by
  classical
  let q' (c : C) : {j // cell (q j) = c} ↪ {p // cell p = c} :=
    ⟨fun j ↦ ⟨q j, j.property⟩, fun a b h ↦ Subtype.ext (hq (congrArg Subtype.val h))⟩
  let u' (c : C) : {j // cell (q j) = c} ↪ {p // cell p = c} :=
    ⟨fun j ↦ ⟨u j, (hc j).symm.trans j.property⟩,
      fun a b h ↦ Subtype.ext (hu (congrArg Subtype.val h))⟩
  let small (c : C) := (q' c).toEquivRange.symm.trans (u' c).toEquivRange
  let whole (c : C) : Equiv.Perm {p // cell p = c} := (small c).extendSubtype
  let e : Equiv.Perm P := Equiv.ofFiberEquiv whole
  refine ⟨e, fun p ↦ Equiv.ofFiberEquiv_map whole p, ?_⟩
  intro j
  have hqmem : (⟨q j, rfl⟩ : {p // cell p = cell (q j)}) ∈ Set.range (q' (cell (q j))) :=
    ⟨⟨j,rfl⟩,rfl⟩
  have hs : whole (cell (q j)) ⟨q j,rfl⟩ = ⟨u j,(hc j).symm⟩ := by
    dsimp only [whole]
    rw [Equiv.extendSubtype_apply_of_mem (small (cell (q j))) _ hqmem]
    change ((small (cell (q j))) ((q' (cell (q j))).toEquivRange ⟨j,rfl⟩)).val = _
    simp only [small, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  change ((whole (cell (q j))) ⟨q j,rfl⟩).val = u j
  exact congrArg Subtype.val hs
