-- Prove2me | solution 1 for SingularModuli.successDensity_le_balanced
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:11:54.252752+00:00
-- url     : https://prove2.me/submissions/cdb35975-bc12-4dee-9d2b-5de3f1252aa0

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

open SingularModuli

open Polynomial Finset FactoringBarriers

namespace SingularModuli

private lemma dvd_prime_mul_cases {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : d ∣ p * q) : d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  have hneq : p * q ≠ 0 := Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'
  by_cases hp_dvd : p ∣ d
  · by_cases hq_dvd : q ∣ d
    · have hcop : p.Coprime q :=
        hp.coprime_iff_not_dvd.mpr fun hpq =>
          hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)
      exact Or.inr (Or.inr (Or.inr
        (Nat.dvd_antisymm h (hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd))))
    · have hcop : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hq_dvd).symm
      have hdp : d ∣ p := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h)
      exact Or.inr (Or.inl (Nat.dvd_antisymm hdp hp_dvd))
  · by_cases hq_dvd : q ∣ d
    · have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hp_dvd).symm
      have hdq : d ∣ q := hcop.dvd_of_dvd_mul_left h
      exact Or.inr (Or.inr (Or.inl (Nat.dvd_antisymm hdq hq_dvd)))
    · left
      by_contra hd1
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hd1
      have hr_dvd : r ∣ p * q := dvd_trans hrd h
      rcases (hrp.dvd_mul.mp hr_dvd) with hrp' | hrq'
      · have hr_eq : r = p := ((Nat.dvd_prime hp).mp hrp').resolve_left hrp.ne_one
        exact hp_dvd (hr_eq ▸ hrd)
      · have hr_eq : r = q := ((Nat.dvd_prime hq).mp hrq').resolve_left hrp.ne_one
        exact hq_dvd (hr_eq ▸ hrd)

private lemma dvd_of_nontrivialDivisor {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (H : Polynomial ℤ) (j : ℤ)
    (h : NontrivialDivisor (p * q) (evalGcd H j (p * q))) :
    (p : ℤ) ∣ H.eval j ∨ (q : ℤ) ∣ H.eval j := by
  obtain ⟨hdvd, h1lt, hlt⟩ := h
  have hgcd_dvd_a : ((evalGcd H j (p * q) : ℕ) : ℤ) ∣ H.eval j := by
    rw [evalGcd]
    exact Int.gcd_dvd_left _ _
  rcases dvd_prime_mul_cases hp hq hne hdvd with h1 | hp' | hq' | hpq
  · omega
  · left
    rw [← hp']
    exact hgcd_dvd_a
  · right
    rw [← hq']
    exact hgcd_dvd_a
  · omega

private lemma redMod_eval_intCast (H : Polynomial ℤ) (m : ℕ) (j : ℤ) :
    (redMod H m).eval (j : ZMod m) = ((H.eval j : ℤ) : ZMod m) := by
  rw [redMod, Polynomial.eval_map, show (j : ZMod m) = Int.castRingHom (ZMod m) j from rfl,
    Polynomial.eval₂_at_apply]
  rfl

private lemma successCount_le_core {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {H : Polynomial ℤ} (hH : H.Monic) :
    successCount H (p * q) ≤ H.natDegree * (p + q) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hcop : p.Coprime q :=
    hp.coprime_iff_not_dvd.mpr fun hpq =>
      hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)
  have hrootP : rootCount H p ≤ H.natDegree := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hmonic : (redMod H p).Monic := hH.map _
    have hne0 : redMod H p ≠ 0 := hmonic.ne_zero
    calc rootCount H p = (redMod H p).roots.toFinset.card := by
          rw [rootCount]
          congr 1
          ext x
          simp only [rootFinset, Finset.mem_filter, Finset.mem_univ, true_and,
            Multiset.mem_toFinset, Polynomial.mem_roots hne0]
          exact Iff.rfl
      _ ≤ (redMod H p).roots.card := Multiset.toFinset_card_le _
      _ ≤ (redMod H p).natDegree := Polynomial.card_roots' _
      _ = H.natDegree := hH.natDegree_map _
  have hrootQ : rootCount H q ≤ H.natDegree := by
    haveI : Fact q.Prime := ⟨hq⟩
    have hmonic : (redMod H q).Monic := hH.map _
    have hne0 : redMod H q ≠ 0 := hmonic.ne_zero
    calc rootCount H q = (redMod H q).roots.toFinset.card := by
          rw [rootCount]
          congr 1
          ext x
          simp only [rootFinset, Finset.mem_filter, Finset.mem_univ, true_and,
            Multiset.mem_toFinset, Polynomial.mem_roots hne0]
          exact Iff.rfl
      _ ≤ (redMod H q).roots.card := Multiset.toFinset_card_le _
      _ ≤ (redMod H q).natDegree := Polynomial.card_roots' _
      _ = H.natDegree := hH.natDegree_map _
  have hsub : successSet H (p * q) ⊆
      ((Finset.range (p * q)).filter (fun j : ℕ => (p : ℤ) ∣ H.eval (j : ℤ)))
        ∪ ((Finset.range (p * q)).filter (fun j : ℕ => (q : ℤ) ∣ H.eval (j : ℤ))) := by
    intro j hj
    rw [successSet, Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases dvd_of_nontrivialDivisor hp hq hne H (j : ℤ) hj.2 with h | h
    · exact Or.inl ⟨hj.1, h⟩
    · exact Or.inr ⟨hj.1, h⟩
  have hpj : ∀ j : ℕ, ((p : ℤ) ∣ H.eval (j : ℤ)) ↔ ((j : ZMod p) ∈ rootFinset H p) := by
    intro j
    have hcast : (j : ZMod p) = ((j : ℤ) : ZMod p) := (Int.cast_natCast (R := ZMod p) j).symm
    rw [rootFinset, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hcast, redMod_eval_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hqj : ∀ j : ℕ, ((q : ℤ) ∣ H.eval (j : ℤ)) ↔ ((j : ZMod q) ∈ rootFinset H q) := by
    intro j
    have hcast : (j : ZMod q) = ((j : ℤ) : ZMod q) := (Int.cast_natCast (R := ZMod q) j).symm
    rw [rootFinset, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hcast, redMod_eval_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcardP : ((Finset.range (p * q)).filter (fun j : ℕ => (p : ℤ) ∣ H.eval (j : ℤ))).card
      = rootCount H p * q := by
    have hbij : ((Finset.range (p * q)).filter (fun j : ℕ => (p : ℤ) ∣ H.eval (j : ℤ))).card
        = (rootFinset H p ×ˢ (Finset.univ : Finset (ZMod q))).card := by
      refine Finset.card_bij (fun j _ => ((j : ZMod p), (j : ZMod q))) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_product]
        exact ⟨(hpj j).mp hj.2, Finset.mem_univ _⟩
      · intro j1 hj1 j2 hj2 heq
        have hj1lt : j1 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
        have hj2lt : j2 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj2).1
        have hm1 : j1 ≡ j2 [MOD p] :=
          ZMod.natCast_eq_natCast_iff _ _ p |>.mp (Prod.ext_iff.mp heq).1
        have hm2 : j1 ≡ j2 [MOD q] :=
          ZMod.natCast_eq_natCast_iff _ _ q |>.mp (Prod.ext_iff.mp heq).2
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm1, hm2⟩ |>.eq_of_lt_of_lt hj1lt hj2lt
      · intro z hz
        have h1 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p) = z.1 :=
          calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p)
              = ((z.1.val : ℕ) : ZMod p) :=
                ZMod.natCast_eq_natCast_iff _ _ p |>.mpr
                  (Nat.chineseRemainder hcop z.1.val z.2.val).2.1
            _ = z.1 := ZMod.natCast_zmod_val z.1
        have h2 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q) = z.2 :=
          calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q)
              = ((z.2.val : ℕ) : ZMod q) :=
                ZMod.natCast_eq_natCast_iff _ _ q |>.mpr
                  (Nat.chineseRemainder hcop z.1.val z.2.val).2.2
            _ = z.2 := ZMod.natCast_zmod_val z.2
        have hlt : (Nat.chineseRemainder hcop z.1.val z.2.val).1 < p * q :=
          Nat.chineseRemainder_lt_mul hcop _ _ (NeZero.ne p) (NeZero.ne q)
        refine ⟨(Nat.chineseRemainder hcop z.1.val z.2.val).1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr hlt,
            (hpj _).mpr (by rw [h1]; exact (Finset.mem_product.mp hz).1)⟩
        · exact Prod.ext h1 h2
    rw [hbij, Finset.card_product, Finset.card_univ, ZMod.card]
    rfl
  have hcardQ : ((Finset.range (p * q)).filter (fun j : ℕ => (q : ℤ) ∣ H.eval (j : ℤ))).card
      = rootCount H q * p := by
    have hbij : ((Finset.range (p * q)).filter (fun j : ℕ => (q : ℤ) ∣ H.eval (j : ℤ))).card
        = ((Finset.univ : Finset (ZMod p)) ×ˢ rootFinset H q).card := by
      refine Finset.card_bij (fun j _ => ((j : ZMod p), (j : ZMod q))) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_product]
        exact ⟨Finset.mem_univ _, (hqj j).mp hj.2⟩
      · intro j1 hj1 j2 hj2 heq
        have hj1lt : j1 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
        have hj2lt : j2 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj2).1
        have hm1 : j1 ≡ j2 [MOD p] :=
          ZMod.natCast_eq_natCast_iff _ _ p |>.mp (Prod.ext_iff.mp heq).1
        have hm2 : j1 ≡ j2 [MOD q] :=
          ZMod.natCast_eq_natCast_iff _ _ q |>.mp (Prod.ext_iff.mp heq).2
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm1, hm2⟩ |>.eq_of_lt_of_lt hj1lt hj2lt
      · intro z hz
        have h1 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p) = z.1 :=
          calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p)
              = ((z.1.val : ℕ) : ZMod p) :=
                ZMod.natCast_eq_natCast_iff _ _ p |>.mpr
                  (Nat.chineseRemainder hcop z.1.val z.2.val).2.1
            _ = z.1 := ZMod.natCast_zmod_val z.1
        have h2 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q) = z.2 :=
          calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q)
              = ((z.2.val : ℕ) : ZMod q) :=
              ZMod.natCast_eq_natCast_iff _ _ q |>.mpr
                  (Nat.chineseRemainder hcop z.1.val z.2.val).2.2
            _ = z.2 := ZMod.natCast_zmod_val z.2
        have hlt : (Nat.chineseRemainder hcop z.1.val z.2.val).1 < p * q :=
          Nat.chineseRemainder_lt_mul hcop _ _ (NeZero.ne p) (NeZero.ne q)
        refine ⟨(Nat.chineseRemainder hcop z.1.val z.2.val).1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr hlt,
            (hqj _).mpr (by rw [h2]; exact (Finset.mem_product.mp hz).2)⟩
        · exact Prod.ext h1 h2
    rw [hbij, Finset.card_product, Finset.card_univ, ZMod.card]
    rw [Nat.mul_comm p ((rootFinset H q).card)]
    rfl
  calc successCount H (p * q)
      = (successSet H (p * q)).card := rfl
    _ ≤ (((Finset.range (p * q)).filter (fun j : ℕ => (p : ℤ) ∣ H.eval (j : ℤ)))
          ∪ ((Finset.range (p * q)).filter (fun j : ℕ => (q : ℤ) ∣ H.eval (j : ℤ)))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range (p * q)).filter (fun j : ℕ => (p : ℤ) ∣ H.eval (j : ℤ))).card
        + ((Finset.range (p * q)).filter (fun j : ℕ => (q : ℤ) ∣ H.eval (j : ℤ))).card :=
        Finset.card_union_le _ _
    _ = rootCount H p * q + rootCount H q * p := by rw [hcardP, hcardQ]
    _ ≤ H.natDegree * q + H.natDegree * p :=
        Nat.add_le_add (Nat.mul_le_mul_right q hrootP) (Nat.mul_le_mul_right p hrootQ)
    _ = H.natDegree * (p + q) := by rw [Nat.mul_add, Nat.add_comm]


private lemma sqrt_balance {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hle : p ≤ q)
    (hbal : q ≤ 3 * p) : (p : ℝ) + q ≤ 4 * Real.sqrt ((p : ℝ) * q) := by
  have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast hp.pos.le
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq.pos.le
  have hpq_le : (p : ℝ) ≤ q := by exact_mod_cast hle
  have hq3p : (q : ℝ) ≤ 3 * p := by exact_mod_cast hbal
  have hs2 : Real.sqrt ((p : ℝ) * q) ^ 2 = (p : ℝ) * q :=
    Real.sq_sqrt (by positivity)
  have h1 : (p : ℝ) * p ≤ (p : ℝ) * q := mul_le_mul_of_nonneg_left hpq_le hp0
  have h2 : (q : ℝ) * q ≤ (3 * p) * q := mul_le_mul_of_nonneg_right hq3p hq0
  have hsq : ((p : ℝ) + q) ^ 2 ≤ (4 * Real.sqrt ((p : ℝ) * q)) ^ 2 := by
    nlinarith [h1, h2, hs2]
  have h3 : |(p : ℝ) + q| ≤ |4 * Real.sqrt ((p : ℝ) * q)| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h3

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hle : p ≤ q) (hbal : q ≤ 3 * p) {H : Polynomial ℤ} (hH : H.Monic) :
    (successCount H (p * q) : ℝ) / (p * q) ≤ 4 * H.natDegree / Real.sqrt (p * q) := by
  push_cast
  have hsc : successCount H (p * q) ≤ H.natDegree * (p + q) := successCount_le_core hp hq hne hH
  have hscR : (successCount H (p * q) : ℝ) ≤ (H.natDegree : ℝ) * ((p : ℝ) + q) := by
    exact_mod_cast hsc
  have hNpos : (0 : ℝ) < (p : ℝ) * q := by
    have h : (0 : ℕ) < p * q := Nat.mul_pos hp.pos hq.pos
    exact_mod_cast h
  have hsqpos : (0 : ℝ) < Real.sqrt ((p : ℝ) * q) := Real.sqrt_pos_of_pos hNpos
  have hsq0 : 0 ≤ Real.sqrt ((p : ℝ) * q) := hsqpos.le
  have hbalR : (p : ℝ) + q ≤ 4 * Real.sqrt ((p : ℝ) * q) := sqrt_balance hp hq hle hbal
  rw [div_le_iff₀ hNpos]
  rw [div_mul_eq_mul_div, le_div_iff₀ hsqpos]
  calc (successCount H (p * q) : ℝ) * Real.sqrt ((p : ℝ) * q)
      ≤ (H.natDegree : ℝ) * ((p : ℝ) + q) * Real.sqrt ((p : ℝ) * q) :=
        mul_le_mul_of_nonneg_right hscR hsq0
    _ ≤ (H.natDegree : ℝ) * (4 * Real.sqrt ((p : ℝ) * q)) * Real.sqrt ((p : ℝ) * q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbalR (Nat.cast_nonneg H.natDegree)) hsq0
    _ = 4 * (H.natDegree : ℝ) * ((p : ℝ) * q) := by
        have hsq2 : Real.sqrt ((p : ℝ) * q) * Real.sqrt ((p : ℝ) * q) = (p : ℝ) * q := by
          rw [← sq, Real.sq_sqrt hNpos.le]
        nlinarith [hsq2]

end SingularModuli

open SingularModuli

theorem solution {p q : ℕ} {H : Polynomial ℤ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hle : p ≤ q) (hbal : q ≤ 3 * p) (hH : H.Monic) :
    (successCount H (p * q) : ℝ) / (p * q) ≤ 4 * H.natDegree / Real.sqrt (p * q) :=
  SingularModuli.solution hp hq hne hle hbal hH

#print axioms solution
