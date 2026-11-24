-- Prove2me | solution 1 for SingularModuli.expected_trials_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:10:55.218086+00:00
-- url     : https://prove2.me/submissions/2f930693-c453-49c2-b1f3-abf2538b5fec

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

private lemma evalGcd_xor_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (H : Polynomial ℤ) (j : ℤ) :
    NontrivialDivisor (p * q) (evalGcd H j (p * q)) ↔
      Xor ((p : ℤ) ∣ H.eval j) ((q : ℤ) ∣ H.eval j) := by
  have hgcd_dvd_a : ((evalGcd H j (p * q) : ℕ) : ℤ) ∣ H.eval j := by
    rw [evalGcd]
    exact Int.gcd_dvd_left _ _
  have hgcd_dvd_N : evalGcd H j (p * q) ∣ p * q := by
    rw [evalGcd]
    exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right _ _)
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr
      (hp.coprime_iff_not_dvd.mpr fun hpq =>
        hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one))
  constructor
  · intro hntr
    obtain ⟨hdvd, h1lt, hlt⟩ := hntr
    rcases dvd_prime_mul_cases hp hq hne hdvd with h1 | hp' | hq' | hpq
    · omega
    · have hpa : (p : ℤ) ∣ H.eval j := by
        rw [← hp']
        exact hgcd_dvd_a
      left
      refine ⟨hpa, fun hqa => ?_⟩
      have hpq_dvd_gcd : p * q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd ?_ (dvd_rfl : ((p * q : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ))
        simpa [Nat.cast_mul] using hcopZ.mul_dvd hpa hqa
      have hpq_le : p * q ≤ evalGcd H j (p * q) := Nat.le_of_dvd (by omega) hpq_dvd_gcd
      rw [hp'] at hpq_le
      nlinarith [hlt, hpq_le]
    · have hqa : (q : ℤ) ∣ H.eval j := by
        rw [← hq']
        exact hgcd_dvd_a
      right
      refine ⟨hqa, fun hpa => ?_⟩
      have hpq_dvd_gcd : p * q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd ?_ (dvd_rfl : ((p * q : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ))
        simpa [Nat.cast_mul] using hcopZ.mul_dvd hpa hqa
      have hpq_le : p * q ≤ evalGcd H j (p * q) := Nat.le_of_dvd (by omega) hpq_dvd_gcd
      rw [hq'] at hpq_le
      nlinarith [hlt, hpq_le]
    · omega
  · intro hx
    rcases hx with ⟨hpa, hnqa⟩ | ⟨hqa, hnpa⟩
    · have hpdvd : p ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd hpa ?_
        simpa [Nat.cast_mul] using dvd_mul_right (p : ℤ) (q : ℤ)
      have hp2 : 2 ≤ p := hp.two_le
      rcases dvd_prime_mul_cases hp hq hne hgcd_dvd_N with h1 | hp' | hq' | hpq
      · exact absurd (Nat.le_of_dvd (by norm_num) (h1 ▸ hpdvd)) (by omega)
      · rw [hp']
        exact ⟨Nat.dvd_mul_right p q, hp.one_lt, by nlinarith [hp.pos, hq.one_lt]⟩
      · have hp_dvd_q : p ∣ q := hq' ▸ hpdvd
        rcases (Nat.dvd_prime hq).mp hp_dvd_q with h | h
        · exact absurd h hp.ne_one
        · exact absurd h hne
      · exact absurd (dvd_trans (by simpa [Nat.cast_mul] using dvd_mul_left (q : ℤ) (p : ℤ))
          (hpq ▸ hgcd_dvd_a)) hnqa
    · have hqdvd : q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd hqa ?_
        simpa [Nat.cast_mul] using dvd_mul_left (q : ℤ) (p : ℤ)
      have hq2 : 2 ≤ q := hq.two_le
      rcases dvd_prime_mul_cases hp hq hne hgcd_dvd_N with h1 | hp' | hq' | hpq
      · exact absurd (Nat.le_of_dvd (by norm_num) (h1 ▸ hqdvd)) (by omega)
      · have hq_dvd_p : q ∣ p := hp' ▸ hqdvd
        rcases (Nat.dvd_prime hp).mp hq_dvd_p with h | h
        · exact absurd h hq.ne_one
        · exact absurd h.symm hne
      · rw [hq']
        exact ⟨Nat.dvd_mul_left q p, hq.one_lt, by nlinarith [hq.pos, hp.one_lt]⟩
      · exact absurd (dvd_trans (by simpa [Nat.cast_mul] using dvd_mul_right (p : ℤ) (q : ℤ))
          (hpq ▸ hgcd_dvd_a)) hnpa

private lemma redMod_eval_intCast (H : Polynomial ℤ) (m : ℕ) (j : ℤ) :
    (redMod H m).eval (j : ZMod m) = ((H.eval j : ℤ) : ZMod m) := by
  rw [redMod, Polynomial.eval_map, show (j : ZMod m) = Int.castRingHom (ZMod m) j from rfl,
    Polynomial.eval₂_at_apply]
  rfl

private lemma successCount_eq_core {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (H : Polynomial ℤ) :
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    haveI : NeZero q := ⟨hq.pos.ne'⟩
    successCount H (p * q)
      = rootCount H p * (q - rootCount H q) + (p - rootCount H p) * rootCount H q := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hcop : p.Coprime q :=
    hp.coprime_iff_not_dvd.mpr fun hpq =>
      hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)
  have hbridge : ∀ j : ℕ,
      NontrivialDivisor (p * q) (evalGcd H (j : ℤ) (p * q)) ↔
        Xor ((j : ZMod p) ∈ rootFinset H p) ((j : ZMod q) ∈ rootFinset H q) := by
    intro j
    rw [evalGcd_xor_iff hp hq hne H (j : ℤ)]
    have hpj : ((p : ℤ) ∣ H.eval (j : ℤ)) ↔ ((j : ZMod p) ∈ rootFinset H p) := by
      have hcast : (j : ZMod p) = ((j : ℤ) : ZMod p) := (Int.cast_natCast (R := ZMod p) j).symm
      rw [rootFinset, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, hcast, redMod_eval_intCast,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hqj : ((q : ℤ) ∣ H.eval (j : ℤ)) ↔ ((j : ZMod q) ∈ rootFinset H q) := by
      have hcast : (j : ZMod q) = ((j : ℤ) : ZMod q) := (Int.cast_natCast (R := ZMod q) j).symm
      rw [rootFinset, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, hcast, redMod_eval_intCast,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hpj, hqj]
  have hstep1 : successCount H (p * q)
      = ((Finset.range (p * q)).filter (fun j : ℕ =>
          Xor ((j : ZMod p) ∈ rootFinset H p) ((j : ZMod q) ∈ rootFinset H q))).card := by
    rw [successCount, successSet, Finset.card_filter, Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : NontrivialDivisor (p * q) (evalGcd H (↑j : ℤ) (p * q))
    · have h' : Xor ((j : ZMod p) ∈ rootFinset H p) ((j : ZMod q) ∈ rootFinset H q) :=
        (hbridge j).mp h
      simp [h, h']
    · have h' : ¬ Xor ((j : ZMod p) ∈ rootFinset H p) ((j : ZMod q) ∈ rootFinset H q) :=
        fun hc => h ((hbridge j).mpr hc)
      simp [h, h']
  have hstep2 : ((Finset.range (p * q)).filter (fun j : ℕ =>
          Xor ((j : ZMod p) ∈ rootFinset H p) ((j : ZMod q) ∈ rootFinset H q))).card
      = (Finset.univ.filter (fun z : ZMod p × ZMod q =>
          Xor (z.1 ∈ rootFinset H p) (z.2 ∈ rootFinset H q))).card := by
    classical
    refine Finset.card_bij (fun j _ => ((j : ZMod p), (j : ZMod q))) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hj.2⟩
    · intro j1 hj1 j2 hj2 heq
      have hj1lt : j1 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
      have hj2lt : j2 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj2).1
      have hp1 : j1 ≡ j2 [MOD p] := ZMod.natCast_eq_natCast_iff _ _ p |>.mp (Prod.ext_iff.mp heq).1
      have hq1 : j1 ≡ j2 [MOD q] := ZMod.natCast_eq_natCast_iff _ _ q |>.mp (Prod.ext_iff.mp heq).2
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hp1, hq1⟩ |>.eq_of_lt_of_lt hj1lt hj2lt
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
          by rw [h1, h2]; exact (Finset.mem_filter.mp hz).2⟩
      · exact Prod.ext h1 h2
  have hstep3 : (Finset.univ.filter (fun z : ZMod p × ZMod q =>
          Xor (z.1 ∈ rootFinset H p) (z.2 ∈ rootFinset H q))).card
      = (rootFinset H p).card * (q - (rootFinset H q).card)
        + (p - (rootFinset H p).card) * (rootFinset H q).card := by
    classical
    have hset : (Finset.univ.filter (fun z : ZMod p × ZMod q =>
          Xor (z.1 ∈ rootFinset H p) (z.2 ∈ rootFinset H q)))
        = rootFinset H p ×ˢ (Finset.univ \ rootFinset H q)
          ∪ (Finset.univ \ rootFinset H p) ×ˢ rootFinset H q := by
      ext z
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_product,
        Finset.mem_sdiff, Finset.mem_sdiff]
      simp only [Finset.mem_univ, true_and, Xor]
      tauto
    have hdisj : Disjoint (rootFinset H p ×ˢ (Finset.univ \ rootFinset H q))
        ((Finset.univ \ rootFinset H p) ×ˢ rootFinset H q) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [Finset.mem_product] at hz1 hz2
      exact (Finset.mem_sdiff.mp hz2.1).2 hz1.1
    rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
      Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ,
      Finset.card_univ, Finset.card_univ, ZMod.card p, ZMod.card q]
  rw [hstep1, hstep2, hstep3]
  rfl

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (H : Polynomial ℤ) (hrp : haveI : NeZero p := ⟨hp.pos.ne'⟩; 1 ≤ rootCount H p)
    (hrq : haveI : NeZero q := ⟨hq.pos.ne'⟩; rootCount H q = 0) (hle : p ≤ q) :
    ((p : ℝ) * q) / successCount H (p * q) ≤ Real.sqrt ((p : ℝ) * q) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hform : successCount H (p * q)
      = rootCount H p * (q - rootCount H q) + (p - rootCount H p) * rootCount H q :=
    successCount_eq_core hp hq hne H
  have hq0 : rootCount H q = 0 := hrq
  have hrp1 : 1 ≤ rootCount H p := hrp
  have hsq : successCount H (p * q) = rootCount H p * q := by
    rw [hform, hq0]
    simp
  have hge : q ≤ successCount H (p * q) := by
    rw [hsq]
    simpa using Nat.mul_le_mul_right q hrp1
  have hscpos_nat : 0 < successCount H (p * q) := lt_of_lt_of_le hq.pos hge
  push_cast
  have hscpos : (0 : ℝ) < (successCount H (p * q) : ℝ) := by exact_mod_cast hscpos_nat
  have hgeR : (q : ℝ) ≤ (successCount H (p * q) : ℝ) := by exact_mod_cast hge
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hNpos : (0 : ℝ) < (p : ℝ) * q := by
    have h : (0 : ℕ) < p * q := Nat.mul_pos hp.pos hq.pos
    exact_mod_cast h
  have hstep1 : ((p : ℝ) * q) / (successCount H (p * q) : ℝ) ≤ (p : ℝ) := by
    rw [div_le_iff₀ hscpos]
    exact mul_le_mul_of_nonneg_left hgeR hp0
  have hleR : (p : ℝ) ≤ q := by exact_mod_cast hle
  have hstep2 : (p : ℝ) ≤ Real.sqrt ((p : ℝ) * q) := by
    rw [Real.le_sqrt hp0 hNpos.le]
    nlinarith [mul_le_mul_of_nonneg_left hleR hp0]
  linarith

end SingularModuli

open SingularModuli

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (H : Polynomial ℤ) (hrp : haveI : NeZero p := ⟨hp.pos.ne'⟩; 1 ≤ rootCount H p)
    (hrq : haveI : NeZero q := ⟨hq.pos.ne'⟩; rootCount H q = 0) (hle : p ≤ q) :
    ((p : ℝ) * q) / successCount H (p * q) ≤ Real.sqrt ((p : ℝ) * q) :=
  SingularModuli.solution hp hq hne H hrp hrq hle

#print axioms solution
