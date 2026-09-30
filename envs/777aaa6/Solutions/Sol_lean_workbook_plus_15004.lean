-- Prove2me | solution 1 for lean_workbook_plus_15004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:07:01.68579+00:00
-- url     : https://prove2.me/submissions/606eb2d7-050b-497b-aebe-7b8faebf08c1

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.NormNum

private theorem square_of_even_factors {n : ℕ} (hn : n ≠ 0)
    (he : ∀ p, Even (n.factorization p)) : IsSquare n := by
  rw [← Nat.factorization_prod_pow_eq_self hn, Finsupp.prod]
  apply Finset.isSquare_prod
  intro p _
  obtain ⟨k, hk⟩ := he p
  exact ⟨p ^ k, by rw [hk, pow_add]⟩

theorem square_product_of_prime_support {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (P : Finset ℕ)
    (hP : ∀ i p, p.Prime → p ∣ a i → p ∈ P)
    (hcard : P.card < Fintype.card ι) :
    ∃ T : Finset ι, T.Nonempty ∧ IsSquare (∏ i ∈ T, a i) := by
  classical
  let v : ι → P → ZMod 2 := fun i p => (a i).factorization p
  have hdep : ¬ LinearIndependent (ZMod 2) v := by
    intro h
    have := h.fintype_card_le_finrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    omega
  obtain ⟨c, hc, i, hci⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let T := Finset.univ.filter (fun i => c i ≠ 0)
  have hprod (p : ℕ) : (∏ j ∈ T, a j).factorization p =
      ∑ j ∈ T, (a j).factorization p := by
    rw [Nat.factorization_prod (fun j _ => (ha j).ne'), Finsupp.finset_sum_apply]
  refine ⟨T, ⟨i, by simp [T, hci]⟩,
    square_of_even_factors (Finset.prod_ne_zero_iff.mpr (fun j _ => (ha j).ne')) ?_⟩
  intro p
  rw [hprod]
  by_cases hp : p ∈ P
  · have hz : ((∑ j ∈ T, (a j).factorization p : ℕ) : ZMod 2) = 0 := by
      have hh := congr_fun hc ⟨p, hp⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [Nat.cast_sum, Finset.sum_filter]
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j _
      have hc01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases hc01 (c j) with h | h <;> simp [h, v]
    exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  · have hzero (j : ι) : (a j).factorization p = 0 := by
      by_cases hprime : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp (hP j p hprime hd))
      · exact Nat.factorization_eq_zero_of_not_prime _ hprime
    simp only [hzero, Finset.sum_const_zero]
    exact ⟨0, rfl⟩

theorem nonempty_bounded_square_product (N : ℕ) (s : Finset ℤ)
    (hs : ∀ x ∈ s, 0 < x ∧ x ≤ N)
    (hcard : ((Finset.range (N + 1)).filter Nat.Prime).card < s.card) :
    ∃ t ⊆ s, t.Nonempty ∧ ∃ z : ℤ, t.prod (fun x => x) = z ^ 2 := by
  classical
  let a : s → ℕ := fun i => i.val.natAbs
  have hcast (i : s) : (a i : ℤ) = i.val := by
    exact (Int.natCast_natAbs i.val).trans (abs_of_nonneg (hs _ i.property).1.le)
  have ha (i : s) : 0 < a i := by
    exact_mod_cast (hcast i).symm ▸ (hs _ i.property).1
  have hP (i : s) (p : ℕ) (hp : p.Prime) (hd : p ∣ a i) :
      p ∈ (Finset.range (N + 1)).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩
    have hle : a i ≤ N := by
      exact_mod_cast (hcast i).symm ▸ (hs _ i.property).2
    have := (Nat.le_of_dvd (ha i) hd).trans hle
    omega
  obtain ⟨T, hT, z, hz⟩ := square_product_of_prime_support a ha
    ((Finset.range (N + 1)).filter Nat.Prime) hP (by simpa using hcard)
  refine ⟨T.image Subtype.val, ?_, hT.image _, (z : ℤ), ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact i.property
  · rw [Finset.prod_image]
    · have hprod : (∏ i ∈ T, i.val) = ((∏ i ∈ T, a i : ℕ) : ℤ) := by
        rw [Nat.cast_prod]
        exact Finset.prod_congr rfl (fun i _ => (hcast i).symm)
      rw [hprod, hz, Nat.cast_mul, pow_two]
    · intro i _ j _ h
      exact Subtype.ext h

theorem hundred_integer_square_subset (s : Finset ℤ)
    (hs : ∀ x ∈ s, 0 < x ∧ x ≤ 199) (hcard : 100 ≤ s.card) :
    ∃ t ⊆ s, t.Nonempty ∧ ∃ z : ℤ, t.prod (fun x => x) = z ^ 2 := by
  apply nonempty_bounded_square_product 199 s hs
  have hp : ((Finset.range 200).filter Nat.Prime).card = 46 := by
    set_option maxRecDepth 4096 in decide
  change ((Finset.range 200).filter Nat.Prime).card < s.card
  omega

theorem solution (s : Finset ℤ) (hs : ∀ x ∈ s, 0 < x ∧ x ≤ 199) :
    ∃ t ⊆ s, ∃ z : ℤ, t.prod (fun x => x) = z ^ 2 := by
  by_cases hc : 100 ≤ s.card
  · obtain ⟨t, hts, _, z, hz⟩ := hundred_integer_square_subset s hs hc
    exact ⟨t, hts, z, hz⟩
  · exact ⟨∅, Finset.empty_subset s, 1, by simp⟩
