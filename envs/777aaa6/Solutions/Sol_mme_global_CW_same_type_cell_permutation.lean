-- Prove2me | solution 1 for mme_global_CW_same_type_cell_permutation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:18:40.448741+00:00
-- url     : https://prove2.me/submissions/3576ad2e-6e75-491b-8cdb-ef4d4447f7b5

import Definitions.Def_mme_global_CW_stage_data
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem cell_fiber {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (a : RecursiveXHash.Address degree R bounds n) (r : Fin R)
    (c : RecursiveThinSplit.Split degree (bounds r)) :
    Fintype.card {p : Place n // cell a p = ⟨r,c⟩} = RecursiveThinSplit.count (a r) c := by
  let e : {p : Place n // cell a p = ⟨r,c⟩} ≃ {t : Fin (n r) // a r t = c} := {
    toFun := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨t,eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun t ↦ ⟨⟨r,t.val⟩,by simp only [cell,t.property]⟩
    left_inv := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro t; rfl }
  rw [Fintype.card_congr e,Fintype.card_subtype]
  rfl

theorem solution {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (a b : RecursiveXHash.Address degree R bounds n)
    (ha : a ∈ RecursiveXHash.target m) (hb : b ∈ RecursiveXHash.target m) :
    ∃ sigma : Equiv.Perm (Place n), ∀ p, cell a (sigma p) = cell b p := by
  have hca := (Finset.mem_filter.mp ha).2
  have hcb := (Finset.mem_filter.mp hb).2
  have hc (c : Cell degree R bounds) :
      Fintype.card {p : Place n // cell b p = c} = Fintype.card {p : Place n // cell a p = c} := by
    rcases c with ⟨r,c⟩
    have h1 := cell_fiber b r c
    have h2 := cell_fiber a r c
    rw [hcb r c] at h1
    rw [hca r c] at h2
    simpa only [Fintype.card_eq_nat_card] using h1.trans h2.symm
  let e := fun c ↦ Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩
