-- Prove2me | solution 1 for hypergraph_turan_fano
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:35:19.728618+00:00
-- url     : https://prove2.me/submissions/fd62ff1e-d263-43c5-9188-eb8f4c60470e

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace OnePointIntersection

def AvoidsSeven {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ¬ ∃ lines : Fin 7 → Finset (Fin n),
    (∀ i, (lines i).card = 3) ∧
    (∀ i j, i ≠ j → (lines i ∩ lines j).card = 1) ∧
    ∀ i, lines i ∈ H

theorem petal_family_card_le {n : ℕ} (H P : Finset (Finset (Fin n)))
    (hH : ∀ e ∈ H, e.card = 3) (hno : AvoidsSeven H) (v : Fin n)
    (hPH : P ⊆ H) (hv : ∀ e ∈ P, v ∈ e)
    (hdis : (P : Set (Finset (Fin n))).Pairwise
      (fun e f => Disjoint (e.erase v) (f.erase v))) : P.card ≤ 6 := by
  classical
  by_contra hcard
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq (show 7 ≤ P.card by omega)
  let E : Q ≃ Fin 7 := Fintype.equivFinOfCardEq (by simpa using hQcard)
  let lines : Fin 7 → Finset (Fin n) := fun i => (E.symm i).1
  apply hno
  refine ⟨lines, ?_, ?_, ?_⟩
  · intro i
    exact hH _ (hPH (hQP (E.symm i).2))
  · intro i j hij
    have hpi : lines i ∈ P := hQP (E.symm i).2
    have hpj : lines j ∈ P := hQP (E.symm j).2
    have hne : lines i ≠ lines j := by
      intro h
      apply hij
      exact E.symm.injective (Subtype.ext h)
    have hd := hdis hpi hpj hne
    have heq : lines i ∩ lines j = {v} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hxi, hxj⟩
        by_contra hxv
        exact Finset.disjoint_left.mp hd
          (Finset.mem_erase.mpr ⟨hxv, hxi⟩) (Finset.mem_erase.mpr ⟨hxv, hxj⟩)
      · rintro rfl
        exact ⟨hv _ hpi, hv _ hpj⟩
    rw [heq, Finset.card_singleton]
  · intro i
    exact hPH (hQP (E.symm i).2)

theorem link_card_le {n : ℕ} (H : Finset (Finset (Fin n)))
    (hH : ∀ e ∈ H, e.card = 3) (hno : AvoidsSeven H) (v : Fin n) :
    (H.filter (fun e => v ∈ e)).card ≤ 12 * n := by
  classical
  let L := H.filter (fun e => v ∈ e)
  let good : Finset (Finset (Fin n)) → Prop := fun P =>
    (P : Set (Finset (Fin n))).Pairwise (fun e f => Disjoint (e.erase v) (f.erase v))
  let choices := L.powerset.filter good
  have hempty : ∅ ∈ choices := by simp [choices, good, Set.Pairwise]
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image choices Finset.card ⟨∅, hempty⟩
  have hPL : P ⊆ L := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hPgood : good P := (Finset.mem_filter.mp hP).2
  have hLH : L ⊆ H := Finset.filter_subset _ _
  have hvL : ∀ e ∈ L, v ∈ e := fun _ he => (Finset.mem_filter.mp he).2
  have hPcard : P.card ≤ 6 :=
    petal_family_card_le H P hH hno v (hPL.trans hLH) (fun e he => hvL e (hPL he)) hPgood
  let K := P.biUnion (fun e => e.erase v)
  have hKcard : K.card ≤ 12 := by
    calc
      K.card ≤ ∑ e ∈ P, (e.erase v).card := Finset.card_biUnion_le
      _ = ∑ _e ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.card_erase_of_mem (hvL e (hPL he)), hH e (hLH (hPL he))]
      _ ≤ 12 := by simpa using (Nat.mul_le_mul_right 2 hPcard)
  have hcover : ∀ e ∈ L, ∃ y ∈ K, y ∈ e := by
    intro e he
    by_contra h
    have haway : ∀ y ∈ K, y ∉ e := by simpa only [not_exists, not_and] using h
    have hnew : ∀ f ∈ P, Disjoint (e.erase v) (f.erase v) := by
      intro f hf
      apply Finset.disjoint_left.mpr
      intro y hye hyf
      exact haway y (Finset.mem_biUnion.mpr ⟨f, hf, hyf⟩) (Finset.mem_of_mem_erase hye)
    have heP : e ∉ P := by
      intro hep
      have hpos : 0 < (e.erase v).card := by
        rw [Finset.card_erase_of_mem (hvL e he), hH e (hLH he)]
        decide
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      exact Finset.disjoint_left.mp (hnew e hep) hy hy
    have hgood : good (insert e P) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hae | haP
      · subst a
        rcases Finset.mem_insert.mp hb with hbe | hbP
        · exact (hab hbe.symm).elim
        · exact hnew b hbP
      · rcases Finset.mem_insert.mp hb with hbe | hbP
        · subst b
          exact (hnew a haP).symm
        · exact hPgood haP hbP hab
    have hchoice : insert e P ∈ choices := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset he hPL), hgood⟩
    have := hmax _ hchoice
    rw [Finset.card_insert_of_notMem heP] at this
    omega
  have hKn : v ∉ K := by simp [K]
  have hsub : L ⊆ (K ×ˢ (Finset.univ : Finset (Fin n))).image
      (fun p => ({v, p.1, p.2} : Finset (Fin n))) := by
    intro e he
    obtain ⟨y, hyK, hye⟩ := hcover e he
    have hyv : y ≠ v := by intro h; exact hKn (h ▸ hyK)
    have hyerase : y ∈ e.erase v := Finset.mem_erase.mpr ⟨hyv, hye⟩
    have hcard : ((e.erase v).erase y).card = 1 := by
      rw [Finset.card_erase_of_mem hyerase, Finset.card_erase_of_mem (hvL e he), hH e (hLH he)]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have heq : e = {v, y, z} := by
      calc
        e = insert v (e.erase v) := (Finset.insert_erase (hvL e he)).symm
        _ = insert v (insert y ((e.erase v).erase y)) := by rw [Finset.insert_erase hyerase]
        _ = {v, y, z} := by rw [hz]
    apply Finset.mem_image.mpr
    exact ⟨(y, z), Finset.mem_product.mpr ⟨hyK, Finset.mem_univ z⟩, heq.symm⟩
  calc
    L.card ≤ ((K ×ˢ (Finset.univ : Finset (Fin n))).image
      (fun p => ({v, p.1, p.2} : Finset (Fin n)))).card := Finset.card_le_card hsub
    _ ≤ (K ×ˢ (Finset.univ : Finset (Fin n))).card := Finset.card_image_le
    _ = K.card * n := by simp
    _ ≤ 12 * n := Nat.mul_le_mul_right n hKcard

theorem total_card_le {n : ℕ} (H : Finset (Finset (Fin n)))
    (hH : ∀ e ∈ H, e.card = 3) (hno : AvoidsSeven H) : H.card ≤ 12 * n ^ 2 := by
  classical
  have hcover : H = Finset.univ.biUnion (fun v : Fin n => H.filter (fun e => v ∈ e)) := by
    ext e
    constructor
    · intro he
      have hpos : 0 < e.card := by rw [hH e he]; decide
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨he, hv⟩⟩
    · intro he
      obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hv).1
  calc
    H.card = (Finset.univ.biUnion (fun v : Fin n => H.filter (fun e => v ∈ e))).card :=
      congrArg Finset.card hcover
    _ ≤ ∑ v : Fin n, (H.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, 12 * n := Finset.sum_le_sum fun v _ => link_card_le H hH hno v
    _ = 12 * n ^ 2 := by simp [pow_two]; ring

end OnePointIntersection

#print axioms OnePointIntersection.link_card_le

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n)
      (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) →
      (¬∃ (lines : Fin 7 → Finset (Fin n)),
        (∀ i, (lines i).card = 3) ∧
        (∀ i j : Fin 7, i ≠ j → (lines i ∩ lines j).card = 1) ∧
        ∀ i, lines i ∈ H) →
      (H.card : ℝ) ≤ (3 / 4 + eps) * Nat.choose n 3 := by
  intro eps heps
  refine ⟨100, ?_⟩
  intro n hn H hH hno
  have hcount : (H.card : ℝ) ≤ 12 * (n : ℝ) ^ 2 := by
    exact_mod_cast OnePointIntersection.total_card_le H hH hno
  have hnat : (n - 2) * (n - 1) * n = 6 * n.choose 3 := by
    simpa [Nat.descFactorial, Nat.factorial, mul_assoc] using
      Nat.descFactorial_eq_factorial_mul_choose n 3
  have hreal := congrArg (fun k : ℕ => (k : ℝ)) hnat
  push_cast at hreal
  rw [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 1 ≤ n by omega)] at hreal
  norm_num at hreal
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hquad : (0 : ℝ) ≤ ((n : ℝ) - 99) * (n : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hbound : 12 * (n : ℝ) ^ 2 ≤ (3 / 4 : ℝ) * (n.choose 3 : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact hcount.trans (hbound.trans (mul_le_mul_of_nonneg_right (by linarith)
    (Nat.cast_nonneg (n.choose 3))))

#print axioms solution
