-- Prove2me | solution 1 for mme_prescribed_cell_sampling_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:35:26.921385+00:00
-- url     : https://prove2.me/submissions/ef38b64c-0bf8-4727-b414-ae38c2fe745a

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem collision_bound {P C J : Type*} [Fintype P] [Fintype J]
    (cell : P → C) (q : J → P) (i j : J) (hij : i ≠ j) :
    Fintype.card {s : (k : J) → {p : P // cell p = cell (q k)} //
      (s i).val = (s j).val} * Fintype.card {p : P // cell p = cell (q i)} ≤
        Fintype.card ((k : J) → {p : P // cell p = cell (q k)}) := by
  classical
  let Samples := (k : J) → {p : P // cell p = cell (q k)}
  let A := {s : Samples // (s i).val = (s j).val}
  let f : A × {p : P // cell p = cell (q i)} → Samples :=
    fun a ↦ Function.update a.1.val i a.2
  have hi : Function.Injective f := by
    rintro ⟨s,p⟩ ⟨t,r⟩ h
    have hp : p = r := by simpa only [f, Function.update_self] using congrFun h i
    have hs : s = t := by
      apply Subtype.ext
      funext k
      by_cases hk : k = i
      · subst k
        apply Subtype.ext
        have hj : (s.val j).val = (t.val j).val := by
          have ht := congrFun h j
          simpa only [f, Function.update_of_ne hij.symm] using congrArg Subtype.val ht
        exact s.property.trans (hj.trans t.property.symm)
      · simpa only [f, Function.update_of_ne hk] using congrFun h k
    exact Prod.ext hs hp
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective f hi

theorem solution {P C J : Type*} [Fintype P] [Fintype J]
    (cell : P → C) (q : J → P) (m : ℕ)
    (hm : ∀ j, m ≤ Fintype.card {p : P // cell p = cell (q j)}) :
    let Samples := (j : J) → {p : P // cell p = cell (q j)}
    m * Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)} ≤
      Fintype.card J ^ 2 * Fintype.card Samples := by
  classical
  let Samples := (j : J) → {p : P // cell p = cell (q j)}
  let bad : Finset Samples := Finset.univ.filter (fun s ↦ ¬ Function.Injective (fun j ↦ (s j).val))
  let pair (v : J × J) : Finset Samples := Finset.univ.filter (fun s ↦ v.1 ≠ v.2 ∧ (s v.1).val = (s v.2).val)
  have hcover : bad ⊆ Finset.univ.biUnion pair := by
    intro s hs
    obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp (Finset.mem_filter.mp hs).2
    exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,he⟩⟩
  have hcard : bad.card ≤ ∑ v : J × J, (pair v).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hp (v : J × J) : m * (pair v).card ≤ Fintype.card Samples := by
    by_cases hn : v.1 = v.2
    · simp [pair, hn]
    · have hb := collision_bound cell q v.1 v.2 hn
      have he : (pair v).card = Fintype.card {s : Samples // (s v.1).val = (s v.2).val} := by
        simp [pair, Fintype.card_subtype, hn]
      rw [he]
      exact (Nat.mul_le_mul_right _ (hm v.1)).trans (by simpa only [Nat.mul_comm] using hb)
  change m * Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)} ≤ _
  rw [Fintype.card_subtype]
  change m * bad.card ≤ _
  calc
    _ ≤ m * ∑ v : J × J, (pair v).card := Nat.mul_le_mul_left m hcard
    _ = ∑ v : J × J, m * (pair v).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _ : J × J, Fintype.card Samples := Finset.sum_le_sum (fun v _ ↦ hp v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul, pow_two]
      rfl
