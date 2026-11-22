-- Prove2me | solution 1 for Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingUpper_markedCell_paper_main_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.223043+00:00
-- url     : https://prove2.me/submissions/a22f1c64-b168-4ddc-867b-b3a63987486e

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_FriableAsymptotic_exists_uniform_friableCount_dickman_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_headDivisorMain_sum_sub_common_le

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero

theorem factorization_factor (q : ℕ) :
    P.factor.factorization q =
      if q ∈ P.primes then P.exponent q else 0 := by
  classical
  rw [factor, Nat.factorization_prod_apply]
  · calc
      ∑ p ∈ P.primes, (p ^ P.exponent p).factorization q =
          ∑ p ∈ P.primes, if p = q then P.exponent p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(P.prime_mem p hp).factorization_pow]
            simp [Finsupp.single_apply]
      _ = if q ∈ P.primes then P.exponent q else 0 := by
        simp [eq_comm]
  · intro p hp
    exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem factor_dvd_of_matches {m : ℕ} (hm : m ≠ 0) (hmatch : P.Matches m) :
    P.factor ∣ m := by
  rw [← Nat.factorization_le_iff_dvd P.factor_ne_zero hm]
  intro q
  rw [P.factorization_factor q]
  split_ifs with hq
  · exact (hmatch q hq).ge
  · exact Nat.zero_le _

theorem exponent_le_of_factor_dvd {m p : ℕ} (hm : m ≠ 0)
    (hfac : P.factor ∣ m) (hp : p ∈ P.primes) :
    P.exponent p ≤ m.factorization p := by
  have hle := (Nat.factorization_le_iff_dvd P.factor_ne_zero hm).mpr hfac p
  simpa [P.factorization_factor p, hp] using hle

/-- Prescribing all head valuations is exactly the condition that the forced
prime-power factor divides `m` and that the remaining quotient contains none
of the head primes.  This is the exact finite identity to which Möbius
inclusion--exclusion is later applied. -/
theorem matches_iff_factor_dvd_and_coprime {m : ℕ} (hm : m ≠ 0) :
    P.Matches m ↔
      P.factor ∣ m ∧ Nat.Coprime (m / P.factor) P.modulus := by
  constructor
  · intro hmatch
    have hfac : P.factor ∣ m := P.factor_dvd_of_matches hm hmatch
    refine ⟨hfac, ?_⟩
    rw [modulus, Nat.coprime_prod_right_iff]
    intro p hp
    apply Nat.Coprime.symm
    apply (P.prime_mem p hp).coprime_iff_not_dvd.mpr
    intro hpdvd
    have hquot_ne : m / P.factor ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hfac)
        (Nat.pos_of_ne_zero P.factor_ne_zero)).ne'
    have hpos := (P.prime_mem p hp).factorization_pos_of_dvd hquot_ne hpdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp, hmatch p hp] at hdiv
    have hzero : (m / P.factor).factorization p = 0 := by
      simpa using hdiv
    omega
  · rintro ⟨hfac, hcop⟩
    intro p hp
    have hhead : Nat.Coprime (m / P.factor) p := by
      rw [modulus, Nat.coprime_prod_right_iff] at hcop
      exact hcop p hp
    have hnotdvd : ¬ p ∣ m / P.factor :=
      (P.prime_mem p hp).coprime_iff_not_dvd.mp hhead.symm
    have hzero : (m / P.factor).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnotdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp] at hdiv
    have hupper : m.factorization p ≤ P.exponent p := by
      apply Nat.sub_eq_zero_iff_le.mp
      exact hdiv.symm.trans hzero
    exact Nat.le_antisymm hupper (P.exponent_le_of_factor_dvd hm hfac hp)





theorem gcd_modulus_ne_zero (k : ℕ) : Nat.gcd k P.modulus ≠ 0 := by
  intro hzero
  have := Nat.gcd_eq_zero_iff.mp hzero
  exact P.modulus_ne_zero this.2



theorem divisors_gcd_eq_filter (k : ℕ) :
    (Nat.gcd k P.modulus).divisors =
      P.modulus.divisors.filter (fun d ↦ d ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hdgcd, _⟩
    exact ⟨⟨(Nat.dvd_gcd_iff.mp hdgcd).2, P.modulus_ne_zero⟩,
      (Nat.dvd_gcd_iff.mp hdgcd).1⟩
  · rintro ⟨⟨hdmod, _⟩, hdk⟩
    exact ⟨Nat.dvd_gcd hdk hdmod, P.gcd_modulus_ne_zero k⟩

/-- The gcd form of `coprimeWeight` is exactly the usual divisor sum
`∑_{d∣M_H} μ(d) 1_{d∣k}` from the paper. -/
theorem coprimeWeight_eq_divisor_sum (k : ℕ) :
    P.coprimeWeight k =
      ∑ d ∈ P.modulus.divisors,
        if d ∣ k then ArithmeticFunction.moebius d else 0 := by
  rw [coprimeWeight, P.divisors_gcd_eq_filter k, Finset.sum_filter]

/-- The exact head-pattern inclusion--exclusion identity, in integral
indicator form. -/
theorem match_indicator_eq_inclusion_exclusion {m : ℕ} (hm : m ≠ 0) :
    (if P.Matches m then (1 : ℤ) else 0) =
      if P.factor ∣ m then
        ∑ d ∈ P.modulus.divisors,
          if d ∣ m / P.factor then ArithmeticFunction.moebius d else 0
      else 0 := by
  rw [← P.coprimeWeight_eq_divisor_sum (m / P.factor)]
  have hiff := P.matches_iff_factor_dvd_and_coprime hm
  by_cases hmatch : P.Matches m
  · obtain ⟨hfac, hcop⟩ := hiff.mp hmatch
    simp [hmatch, hfac, hcop]
  · by_cases hfac : P.factor ∣ m
    · have hnotcop : ¬ Nat.Coprime (m / P.factor) P.modulus := by
        intro hcop
        exact hmatch (hiff.mpr ⟨hfac, hcop⟩)
      simp [hmatch, hfac, hnotcop]
    · simp [hmatch, hfac]

end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.StructuredCells -/
section


/-!
# Exact structured-cell reductions

This file defines the actual finite smooth intervals and exact head cells.
It proves the finite inclusion--exclusion identity before any use of a
friable-number asymptotic.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCells

open HeadPattern













theorem smoothNumbersUpTo_mono {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    Nat.smoothNumbersUpTo X₁ (y + 1) ⊆
      Nat.smoothNumbersUpTo X₂ (y + 1) := by
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

/-- An exact interval count is a difference of two `psi` values. -/
theorem smoothInterval_card_eq_psi_sub {lo hi y : ℕ} (hlohi : lo ≤ hi) :
    (smoothInterval lo hi y).card = psi hi y - psi lo y := by
  have hset : smoothInterval lo hi y =
      Nat.smoothNumbersUpTo hi (y + 1) \
        Nat.smoothNumbersUpTo lo (y + 1) := by
    ext m
    simp only [mem_smoothInterval, Finset.mem_sdiff,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hlom, hmhi, hsmooth⟩
      exact ⟨⟨hmhi, hsmooth⟩, fun hlow ↦ (Nat.not_le_of_lt hlom) hlow.1⟩
    · rintro ⟨⟨hmhi, hsmooth⟩, hnotlow⟩
      refine ⟨?_, hmhi, hsmooth⟩
      by_contra hnlt
      exact hnotlow ⟨Nat.le_of_not_gt hnlt, hsmooth⟩
  rw [hset, Finset.card_sdiff]
  have hinter :
      Nat.smoothNumbersUpTo lo (y + 1) ∩
          Nat.smoothNumbersUpTo hi (y + 1) =
        Nat.smoothNumbersUpTo lo (y + 1) := by
    exact Finset.inter_eq_left.mpr (smoothNumbersUpTo_mono hlohi)
  rw [hinter]
  rfl





theorem coprime_factor_of_coprime_modulus (P : Pattern) {d : ℕ}
    (hcop : Nat.Coprime d P.modulus) : Nat.Coprime d P.factor := by
  rw [Pattern.factor, Nat.coprime_prod_right_iff]
  intro p hp
  apply Nat.Coprime.pow_right
  rw [Pattern.modulus, Nat.coprime_prod_right_iff] at hcop
  exact hcop p hp

theorem pow_mem_smoothNumbers {z p : ℕ}
    (hp : p ∈ Nat.smoothNumbers z) (e : ℕ) :
    p ^ e ∈ Nat.smoothNumbers z := by
  induction e with
  | zero => simp [Nat.mem_smoothNumbers]
  | succ e ih =>
      rw [pow_succ]
      exact Nat.mul_mem_smoothNumbers ih hp

theorem factor_mem_smoothNumbers (P : Pattern) {y : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y) :
    P.factor ∈ Nat.smoothNumbers (y + 1) := by
  rw [Pattern.factor]
  apply Finset.prod_induction (s := P.primes)
    (fun p ↦ p ^ P.exponent p)
    (fun z ↦ z ∈ Nat.smoothNumbers (y + 1))
    (fun _ _ ha hb ↦ Nat.mul_mem_smoothNumbers ha hb)
    (by simp [Nat.mem_smoothNumbers])
  intro p hp
  apply pow_mem_smoothNumbers
  exact Nat.mem_smoothNumbers_of_lt (P.prime_mem p hp).pos
    (Nat.lt_succ_of_le (hhead p hp))

theorem modulus_mem_smoothNumbers (P : Pattern) {y : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y) :
    P.modulus ∈ Nat.smoothNumbers (y + 1) := by
  rw [Pattern.modulus]
  apply Finset.prod_induction (s := P.primes)
    (fun p ↦ p)
    (fun z ↦ z ∈ Nat.smoothNumbers (y + 1))
    (fun _ _ ha hb ↦ Nat.mul_mem_smoothNumbers ha hb)
    (by simp [Nat.mem_smoothNumbers])
  intro p hp
  exact Nat.mem_smoothNumbers_of_lt (P.prime_mem p hp).pos
    (Nat.lt_succ_of_le (hhead p hp))

/-- Under the paper's coprimality condition `(d,M_H)=1`, the three
divisibility conditions appearing after head inclusion--exclusion combine
into one marked divisor. -/
theorem combined_dvd_iff (P : Pattern) {m d a : ℕ}
    (hcop : Nat.Coprime d P.modulus) (ha : a ∣ P.modulus) :
    (d ∣ m ∧ P.factor ∣ m ∧ a ∣ m / P.factor) ↔
      P.factor * a * d ∣ m := by
  constructor
  · rintro ⟨hd, hfac, haquot⟩
    have hfa : P.factor * a ∣ m :=
      (Nat.dvd_div_iff_mul_dvd hfac).mp haquot
    have hcopa : Nat.Coprime d a := Nat.Coprime.of_dvd_right ha hcop
    have hcopfa : Nat.Coprime d (P.factor * a) :=
      (coprime_factor_of_coprime_modulus P hcop).mul_right hcopa
    have hprod : d * (P.factor * a) ∣ m :=
      hcopfa.mul_dvd_of_dvd_of_dvd hd hfa
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  · intro hprod
    have hfac : P.factor ∣ m :=
      (dvd_mul_right P.factor (a * d)).trans (by
        simpa [mul_assoc] using hprod)
    have hd : d ∣ m := by
      have : d ∣ P.factor * a * d := by simp
      exact this.trans hprod
    refine ⟨hd, hfac, ?_⟩
    apply (Nat.dvd_div_iff_mul_dvd hfac).mpr
    have : P.factor * a ∣ P.factor * a * d := dvd_mul_right _ _
    exact this.trans hprod

/-- Exact reindexing of smooth multiples by division.  This is the finite
identity that turns each inclusion--exclusion term into a difference of two
friable counting functions. -/
theorem smooth_multiple_card_eq_quotient_interval {lo hi y D : ℕ}
    (hDpos : 0 < D) (hDsmooth : D ∈ Nat.smoothNumbers (y + 1)) :
    ((smoothInterval lo hi y).filter (D ∣ ·)).card =
      (smoothInterval (lo / D) (hi / D) y).card := by
  classical
  apply Finset.card_bij (fun m _ ↦ m / D)
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hminterval, hDvd⟩ := hm
    obtain ⟨hlom, hmhi, hsmooth⟩ := mem_smoothInterval.mp hminterval
    apply mem_smoothInterval.mpr
    refine ⟨(Nat.div_lt_iff_lt_mul hDpos).mpr ?_,
      (Nat.le_div_iff_mul_le hDpos).mpr ?_, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using hlom
    · simpa [Nat.div_mul_cancel hDvd] using hmhi
    · exact Nat.mem_smoothNumbers_of_dvd hsmooth (Nat.div_dvd_of_dvd hDvd)
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / D * D := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / D * D := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    refine ⟨k * D, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, by simp⟩
      obtain ⟨hlok, hkhi, hksmooth⟩ := mem_smoothInterval.mp hk
      apply mem_smoothInterval.mpr
      exact ⟨(Nat.div_lt_iff_lt_mul hDpos).mp hlok,
        (Nat.le_div_iff_mul_le hDpos).mp hkhi,
        Nat.mul_mem_smoothNumbers hksmooth hDsmooth⟩
    · exact Nat.mul_div_left k hDpos

/-- Exact finite count reduction corresponding to the paper's head-pattern
inclusion--exclusion formula.  The right side contains only ordinary smooth
multiple counts; no asymptotic estimate has entered. -/
theorem markedCell_card_inclusion_exclusion (P : Pattern)
    {lo hi y d : ℕ} (hcop : Nat.Coprime d P.modulus) :
    ((markedCell P lo hi y d).card : ℤ) =
      ∑ a ∈ P.modulus.divisors,
        ArithmeticFunction.moebius a *
          (((smoothInterval lo hi y).filter
            (P.factor * a * d ∣ ·)).card : ℤ) := by
  classical
  rw [markedCell]
  simp only [structuredCell, Finset.filter_filter]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ m ∈ smoothInterval lo hi y,
        if P.Matches m ∧ d ∣ m then (1 : ℤ) else 0) =
      ∑ m ∈ smoothInterval lo hi y,
        if d ∣ m then
          (if P.factor ∣ m then
            ∑ a ∈ P.modulus.divisors,
              if a ∣ m / P.factor then ArithmeticFunction.moebius a else 0
           else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm0 : m ≠ 0 := (pos_of_mem_smoothInterval hm).ne'
          by_cases hd : d ∣ m
          · simpa [hd, and_comm] using
              P.match_indicator_eq_inclusion_exclusion hm0
          · simp [hd]
    _ = ∑ a ∈ P.modulus.divisors,
        ArithmeticFunction.moebius a *
          (((smoothInterval lo hi y).filter
            (P.factor * a * d ∣ ·)).card : ℤ) := by
      have hpoint (m : ℕ) :
          (if d ∣ m then
            (if P.factor ∣ m then
              ∑ a ∈ P.modulus.divisors,
                if a ∣ m / P.factor then ArithmeticFunction.moebius a else 0
             else 0)
           else 0) =
            ∑ a ∈ P.modulus.divisors,
              ArithmeticFunction.moebius a *
                if P.factor * a * d ∣ m then 1 else 0 := by
        by_cases hd : d ∣ m
        · rw [if_pos hd]
          by_cases hfac : P.factor ∣ m
          · rw [if_pos hfac]
            apply Finset.sum_congr rfl
            intro a haDiv
            have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
            have hiff := combined_dvd_iff P (m := m) (d := d) (a := a) hcop ha
            by_cases haq : a ∣ m / P.factor
            · have hprod : P.factor * a * d ∣ m :=
                hiff.mp ⟨hd, hfac, haq⟩
              simp [haq, hprod]
            · have hnprod : ¬ P.factor * a * d ∣ m := by
                intro hprod
                exact haq (hiff.mpr hprod).2.2
              simp [haq, hnprod]
          · rw [if_neg hfac]
            symm
            apply Finset.sum_eq_zero
            intro a haDiv
            have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
            have hnprod : ¬ P.factor * a * d ∣ m := by
              intro hprod
              exact hfac (combined_dvd_iff P hcop ha |>.mpr hprod).2.1
            simp [hnprod]
        · rw [if_neg hd]
          symm
          apply Finset.sum_eq_zero
          intro a haDiv
          have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
          have hnprod : ¬ P.factor * a * d ∣ m := by
            intro hprod
            exact hd (combined_dvd_iff P hcop ha |>.mpr hprod).1
          simp [hnprod]
      simp_rw [hpoint]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a haDiv
      rw [← Finset.mul_sum]
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]



end Erdos390.Full.StructuredCells

end

/- Source module: Erdos390.Full.Scale -/
section


/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel















/-- Four marked prime factors use precisely the exponent `8/9`. -/
theorem y_pow_four (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) := by
  calc
    y n ^ 4 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 4 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (4 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 4).symm
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := by norm_num



/-- The smallest cofactor after four marks is exactly `n^(1/9)`. -/
theorem cofactor_four {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / y n ^ 4 = (n : ℝ) ^ (1 / 9 : ℝ) := by
  rw [y_pow_four]
  calc
    (n : ℝ) / (n : ℝ) ^ (8 / 9 : ℝ) =
        (n : ℝ) ^ ((1 : ℝ) - 8 / 9) := by
          rw [Real.rpow_sub (by exact_mod_cast hn), Real.rpow_one]
    _ = (n : ℝ) ^ (1 / 9 : ℝ) := by norm_num









end Erdos390.Full.Scale

end

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/

























theorem friableCount_mono_left {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    friableCount X₁ y ≤ friableCount X₂ y := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩







/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring

















/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower

/-- Uniform Dickman estimate with the exact initial face included. -/
theorem exists_uniform_friableCount_dickman_bound_all_faces :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₁, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound
  refine ⟨K, hK, max 2 Y₁, ?_⟩
  intro X y hy hX hlog
  have hy2 : 2 ≤ y := (le_max_left 2 Y₁).trans hy
  have hY₁y : Y₁ ≤ y := (le_max_right 2 Y₁).trans hy
  by_cases hyX : y ≤ X
  · exact hmain hY₁y hyX hlog
  · have hXy : X ≤ y := le_of_not_ge hyX
    rw [friableCount_eq_dickman_initial hX (by omega) hXy,
      sub_self, abs_zero]
    positivity




end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.Full.MarkedFriableAsymptotic -/
section


open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology Asymptotics

namespace Erdos390.Full.MarkedFriableAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern

theorem psi_eq_friableCount (X y : ℕ) :
    psi X y = FriableAsymptotic.friableCount X y := rfl

/-- The uniform Dickman estimate, including the zero endpoint. -/
theorem exists_uniform_psi_dickman_bound_all_endpoints :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(psi X y : ℝ) -
          (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hmain⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y hy hlog
  by_cases hX : X = 0
  · subst X
    simp [psi, FriableAsymptotic.dickmanU]
  · simpa only [psi_eq_friableCount] using
      hmain hy (Nat.pos_of_ne_zero hX) hlog

/-- Difference form for an actual smooth interval. -/
theorem exists_uniform_smoothInterval_dickman_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {lo hi y : ℕ},
      Y₀ ≤ y → lo ≤ hi →
      Real.log (lo : ℝ) ≤ 5 * Real.log (y : ℝ) →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |((smoothInterval lo hi y).card : ℝ) -
          ((hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y))| ≤
        K * ((hi : ℝ) + (lo : ℝ)) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hpoint⟩ :=
    exists_uniform_psi_dickman_bound_all_endpoints
  refine ⟨K, hK, Y₀, ?_⟩
  intro lo hi y hy hlohi hloglo hloghi
  have hpsi : psi lo y ≤ psi hi y := by
    exact FriableAsymptotic.friableCount_mono_left hlohi
  have hhi := hpoint hy hloghi
  have hlo := hpoint hy hloglo
  rw [smoothInterval_card_eq_psi_sub hlohi]
  rw [Nat.cast_sub hpsi]
  calc
    _ = |(((psi hi y : ℝ) -
            (hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y)) -
          ((psi lo y : ℝ) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y)))| := by ring_nf
    _ ≤ |(psi hi y : ℝ) -
            (hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y)| +
          |(psi lo y : ℝ) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y)| := by
      have h := abs_sub_le
        ((psi hi y : ℝ) - (hi : ℝ) *
          rho (FriableAsymptotic.dickmanU hi y)) 0
        ((psi lo y : ℝ) - (lo : ℝ) *
          rho (FriableAsymptotic.dickmanU lo y))
      simpa only [sub_zero, zero_sub, abs_neg] using h
    _ ≤ K * (hi : ℝ) / Real.log (y : ℝ) +
          K * (lo : ℝ) / Real.log (y : ℝ) := add_le_add hhi hlo
    _ = K * ((hi : ℝ) + (lo : ℝ)) / Real.log (y : ℝ) := by ring

end Erdos390.Full.MarkedFriableAsymptotic

end

/- Source module: Erdos390.Full.StructuredCellAsymptotic -/
section


/-!
# Unconditional Dickman estimate for the actual structured cells

This file composes the exact head-pattern inclusion--exclusion identity with
the proved uniform friable-number estimate.  In particular, the theorem below
does not assume a marked-cell asymptotic: its only analytic hypotheses are the
explicit logarithmic-range inequalities at the finitely many endpoints.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCellAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic





/-- Real-cast form of the exact finite inclusion--exclusion identity, after
reindexing every smooth multiple by division. -/
theorem markedCell_card_real_eq_smoothInterval_sum
    (P : Pattern) {lo hi y d : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y)
    (hdpos : 0 < d) (hdsmooth : d ∈ Nat.smoothNumbers (y + 1))
    (hcop : Nat.Coprime d P.modulus) :
    ((markedCell P lo hi y d).card : ℝ) =
      ∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) *
          ((smoothInterval (lo / (P.factor * a * d))
            (hi / (P.factor * a * d)) y).card : ℝ) := by
  have hZ := markedCell_card_inclusion_exclusion P
    (lo := lo) (hi := hi) (y := y) (d := d) hcop
  have h := congrArg (fun z : ℤ ↦ (z : ℝ)) hZ
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at h
  calc
    ((markedCell P lo hi y d).card : ℝ) =
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) *
            (((smoothInterval lo hi y).filter
              (P.factor * a * d ∣ ·)).card : ℝ) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a haDiv
      have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
      have hapos : 0 < a :=
        Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero P.modulus_ne_zero)
      have hDpos : 0 < P.factor * a * d :=
        mul_pos (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero) hapos) hdpos
      have haSmooth : a ∈ Nat.smoothNumbers (y + 1) :=
        Nat.mem_smoothNumbers_of_dvd (modulus_mem_smoothNumbers P hhead) ha
      have hDSmooth : P.factor * a * d ∈ Nat.smoothNumbers (y + 1) :=
        Nat.mul_mem_smoothNumbers
          (Nat.mul_mem_smoothNumbers
            (factor_mem_smoothNumbers P hhead) haSmooth)
          hdsmooth
      rw [smooth_multiple_card_eq_quotient_interval hDpos hDSmooth]

/-- The actual marked structured-cell count is uniformly approximated by
the finite sum of Dickman endpoint main terms.  The error ledger is written
term by term, so no unproved dependence on the fixed head pattern is hidden.
-/
theorem exists_uniform_markedCell_dickman_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ (P : Pattern) {lo hi y d : ℕ},
      Y₀ ≤ y → lo ≤ hi →
      (∀ p ∈ P.primes, p ≤ y) →
      0 < d → d ∈ Nat.smoothNumbers (y + 1) →
      Nat.Coprime d P.modulus →
      (∀ a ∈ P.modulus.divisors,
        Real.log ((lo / (P.factor * a * d) : ℕ) : ℝ) ≤
          5 * Real.log (y : ℝ)) →
      (∀ a ∈ P.modulus.divisors,
        Real.log ((hi / (P.factor * a * d) : ℕ) : ℝ) ≤
          5 * Real.log (y : ℝ)) →
      |((markedCell P lo hi y d).card : ℝ) -
          ∑ a ∈ P.modulus.divisors, headDivisorMain P lo hi y d a| ≤
        ∑ a ∈ P.modulus.divisors,
          |(ArithmeticFunction.moebius a : ℝ)| *
            (K *
              (((hi / (P.factor * a * d) : ℕ) : ℝ) +
                ((lo / (P.factor * a * d) : ℕ) : ℝ)) /
              Real.log (y : ℝ)) := by
  obtain ⟨K, hK, Y₀, hinterval⟩ :=
    exists_uniform_smoothInterval_dickman_bound
  refine ⟨K, hK, Y₀, ?_⟩
  intro P lo hi y d hy hlohi hhead hdpos hdsmooth hcop hloglo hloghi
  rw [markedCell_card_real_eq_smoothInterval_sum P hhead hdpos
    hdsmooth hcop]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a ∈ P.modulus.divisors,
          ((ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval (lo / (P.factor * a * d))
                (hi / (P.factor * a * d)) y).card : ℝ) -
            headDivisorMain P lo hi y d a)| ≤
        ∑ a ∈ P.modulus.divisors,
        |((ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval (lo / (P.factor * a * d))
                (hi / (P.factor * a * d)) y).card : ℝ) -
            headDivisorMain P lo hi y d a)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K *
            (((hi / (P.factor * a * d) : ℕ) : ℝ) +
              ((lo / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (y : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      let Xhi := hi / (P.factor * a * d)
      let Xlo := lo / (P.factor * a * d)
      have hXlohi : Xlo ≤ Xhi := Nat.div_le_div_right hlohi
      have hinter := hinterval hy hXlohi (hloglo a ha) (hloghi a ha)
      have herr :
          |((smoothInterval Xlo Xhi y).card : ℝ) -
              (endpointMain Xhi y - endpointMain Xlo y)| ≤
            K * ((Xhi : ℝ) + (Xlo : ℝ)) / Real.log (y : ℝ) := by
        simpa only [endpointMain] using hinter
      rw [show
        (ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval Xlo Xhi y).card : ℝ) -
            headDivisorMain P lo hi y d a =
          (ArithmeticFunction.moebius a : ℝ) *
            (((smoothInterval Xlo Xhi y).card : ℝ) -
              (endpointMain Xhi y - endpointMain Xlo y)) by
        simp only [headDivisorMain, Xhi, Xlo]
        ring]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Xhi, Xlo] using herr) (abs_nonneg _)

end Erdos390.Full.StructuredCellAsymptotic

end

/- Source module: Erdos390.Full.PaperScaleEndpoint -/
section


/-! Quantitative endpoint specialization at the paper scale. -/

namespace Erdos390.Full.PaperScaleMarkedCell









theorem log_y_sub_log_yNat_bounds {n : ℕ} (hn : 0 < n)
    (hy2 : 2 ≤ ArithmeticModel.y n) :
    0 ≤ Real.log (ArithmeticModel.y n) -
          Real.log (ArithmeticModel.yNat n : ℝ) ∧
      Real.log (ArithmeticModel.y n) -
          Real.log (ArithmeticModel.yNat n : ℝ) ≤ Real.log 2 := by
  have hypos : 0 < ArithmeticModel.y n := Scale.y_pos hn
  have hyNatUpper : (ArithmeticModel.yNat n : ℝ) ≤ ArithmeticModel.y n :=
    Nat.floor_le hypos.le
  have hyNatLower : ArithmeticModel.y n / 2 ≤
      (ArithmeticModel.yNat n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (ArithmeticModel.y n)
    change ArithmeticModel.y n <
      (ArithmeticModel.yNat n : ℝ) + 1 at hfloor
    linarith
  have hyNatPos : (0 : ℝ) < (ArithmeticModel.yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogUpper : Real.log (ArithmeticModel.yNat n : ℝ) ≤
      Real.log (ArithmeticModel.y n) :=
    Real.log_le_log hyNatPos hyNatUpper
  have hlogLower : Real.log (ArithmeticModel.y n / 2) ≤
      Real.log (ArithmeticModel.yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (ArithmeticModel.y n / 2) =
      Real.log (ArithmeticModel.y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hlogDiv] at hlogLower
  constructor <;> linarith









private theorem endpoint_ideal_lower_bound
    (P : HeadPattern.Pattern) (C : ℝ) {n a d : ℕ}
    (hC : 0 < C) (hn : 0 < n)
    (ha : a ∈ P.modulus.divisors) (hd : 0 < d)
    (hyNat : 0 < ArithmeticModel.yNat n)
    (hd4 : d ≤ ArithmeticModel.yNat n ^ 4) :
    (C / ((P.factor * P.modulus : ℕ) : ℝ)) *
        (n : ℝ) ^ (1 / 9 : ℝ) ≤
      C * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) := by
  have hfactor : 0 < P.factor := Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : 0 < P.modulus := Nat.pos_of_ne_zero P.modulus_ne_zero
  have haPos : 0 < a := Nat.pos_of_mem_divisors ha
  have haLe : a ≤ P.modulus :=
    Nat.le_of_dvd hmod (Nat.dvd_of_mem_divisors ha)
  have hq : P.factor * a * d ≤
      (P.factor * P.modulus) * ArithmeticModel.yNat n ^ 4 := by
    gcongr
  have hqPos : 0 < P.factor * a * d := by positivity
  have hQPos : 0 <
      (P.factor * P.modulus) * ArithmeticModel.yNat n ^ 4 := by positivity
  have hnum : 0 ≤ C * (n : ℝ) := by positivity
  have hdenMono :
      C * (n : ℝ) /
          (((P.factor * P.modulus) * ArithmeticModel.yNat n ^ 4 : ℕ) : ℝ) ≤
        C * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_left hnum
    · exact_mod_cast hqPos
    · exact_mod_cast hq
  have hyFloor : (ArithmeticModel.yNat n : ℝ) ≤ ArithmeticModel.y n :=
    Nat.floor_le (Scale.y_pos hn).le
  have hyPow : (ArithmeticModel.yNat n : ℝ) ^ 4 ≤
      ArithmeticModel.y n ^ 4 := by gcongr
  have hcofactor :
      (n : ℝ) / ArithmeticModel.y n ^ 4 ≤
        (n : ℝ) / (ArithmeticModel.yNat n : ℝ) ^ 4 := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n)
    · positivity
    · exact hyPow
  calc
    (C / ((P.factor * P.modulus : ℕ) : ℝ)) *
        (n : ℝ) ^ (1 / 9 : ℝ) =
      (C / ((P.factor * P.modulus : ℕ) : ℝ)) *
        ((n : ℝ) / ArithmeticModel.y n ^ 4) := by
      rw [Scale.cofactor_four hn]
    _ ≤ (C / ((P.factor * P.modulus : ℕ) : ℝ)) *
        ((n : ℝ) / (ArithmeticModel.yNat n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hcofactor (by positivity)
    _ = C * (n : ℝ) /
        (((P.factor * P.modulus) * ArithmeticModel.yNat n ^ 4 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow]
      ring
    _ ≤ _ := hdenMono

theorem exists_endpoint_margin_threshold
    (P : HeadPattern.Pattern) {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ {n a d : ℕ}, N₀ ≤ n →
      a ∈ P.modulus.divisors → 0 < d →
      d ≤ ArithmeticModel.yNat n ^ 4 →
      4 ≤ C * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      Scale.L n ≤ C * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) := by
  let k : ℝ := C / ((P.factor * P.modulus : ℕ) : ℝ)
  have hG : (0 : ℝ) < ((P.factor * P.modulus : ℕ) : ℝ) := by
    exact_mod_cast mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
      (Nat.pos_of_ne_zero P.modulus_ne_zero)
  have hk : 0 < k := div_pos hC hG
  have hpowTop : Filter.Tendsto (fun n : ℕ =>
      (n : ℝ) ^ (1 / 9 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp
      tendsto_natCast_atTop_atTop
  have hpowEvent : ∀ᶠ n : ℕ in Filter.atTop,
      4 / k ≤ (n : ℝ) ^ (1 / 9 : ℝ) :=
    hpowTop.eventually (Filter.eventually_ge_atTop (4 / k))
  have hratioReal : Filter.Tendsto
      (fun x : ℝ => Real.log x / x ^ (1 / 9 : ℝ))
      Filter.atTop (nhds 0) :=
    by
      simpa using
        (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
          (by norm_num : (0 : ℝ) < 1 / 9)).tendsto_div_nhds_zero
  have hratioNat : Filter.Tendsto
      (fun n : ℕ => Scale.L n / (n : ℝ) ^ (1 / 9 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Scale.L, Real.rpow_one] using
      hratioReal.comp tendsto_natCast_atTop_atTop
  have hratioEvent : ∀ᶠ n : ℕ in Filter.atTop,
      Scale.L n / (n : ℝ) ^ (1 / 9 : ℝ) < k :=
    (tendsto_order.1 hratioNat).2 k hk
  have hlogEvent := FriableAsymptotic.eventually_one_fifth_L_le_log_yNat
  have hAll : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧
      4 / k ≤ (n : ℝ) ^ (1 / 9 : ℝ) ∧
      Scale.L n / (n : ℝ) ^ (1 / 9 : ℝ) < k ∧
      (1 / 5 : ℝ) * Scale.L n ≤
        Real.log (ArithmeticModel.yNat n : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hpowEvent,
      hratioEvent, hlogEvent] with n hn hpow hratio hlog
    exact ⟨hn, hpow, hratio, hlog⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨N₀, ?_⟩
  intro n a d hNn ha hd hd4
  obtain ⟨hn, hpow, hratio, hlog⟩ := hN₀ n hNn
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  have hyLog : 0 < Real.log (ArithmeticModel.yNat n : ℝ) :=
    (by positivity : 0 < (1 / 5 : ℝ) * Scale.L n).trans_le hlog
  have hyNat : 0 < ArithmeticModel.yNat n := by
    have hyOne : (1 : ℝ) < (ArithmeticModel.yNat n : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hyLog
    exact_mod_cast (zero_lt_one.trans hyOne)
  have hlower := endpoint_ideal_lower_bound P C hC hnpos ha hd hyNat hd4
  have hfour : 4 ≤ k * (n : ℝ) ^ (1 / 9 : ℝ) := by
    calc
      (4 : ℝ) = k * (4 / k) := by field_simp [hk.ne']
      _ ≤ k * (n : ℝ) ^ (1 / 9 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hk.le
  have hpowPos : 0 < (n : ℝ) ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
  have hlogMargin : Scale.L n ≤
      k * (n : ℝ) ^ (1 / 9 : ℝ) := by
    exact ((div_lt_iff₀ hpowPos).mp hratio).le
  simpa only [k] using
    And.intro (hfour.trans hlower) (hlogMargin.trans hlower)

/-- For a fixed positive physical endpoint `C`, every quotient below
`floor(C n)` lies in the `u ≤ 5` logarithmic range once `n` is large.
The threshold is independent of the quotient modulus. -/
theorem exists_physicalBound_log_range
    {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ {n q : ℕ}, N₀ ≤ n → 0 < q →
      Real.log (((ArithmeticModel.physicalBound C n) / q : ℕ) : ℝ) ≤
        5 * Real.log (ArithmeticModel.yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => ArithmeticModel.y n)
      Filter.atTop Filter.atTop := by
    simpa [ArithmeticModel.y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto Scale.L Filter.atTop Filter.atTop := by
    simpa [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyEvent : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ ArithmeticModel.y n :=
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  have hLEvent : ∀ᶠ n : ℕ in Filter.atTop,
      9 * (Real.log C + 5 * Real.log 2) ≤ Scale.L n :=
    hLTop.eventually
      (Filter.eventually_ge_atTop (9 * (Real.log C + 5 * Real.log 2)))
  have hAll : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ 2 ≤ ArithmeticModel.y n ∧
        9 * (Real.log C + 5 * Real.log 2) ≤ Scale.L n := by
    filter_upwards [Filter.eventually_gt_atTop 1, hyEvent, hLEvent] with
      n hn hy hL
    exact ⟨hn, hy, hL⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨N₀, ?_⟩
  intro n q hNn hq
  obtain ⟨hn, hy2, hLlarge⟩ := hN₀ n hNn
  have hnpos : 0 < n := by omega
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hyGap := log_y_sub_log_yNat_bounds hnpos hy2
  have ht : Real.log (ArithmeticModel.y n) =
      (2 / 9 : ℝ) * Scale.L n := Scale.log_y hnpos
  have hspos : 0 < Real.log (ArithmeticModel.yNat n : ℝ) := by
    have hyNat2 : 2 ≤ ArithmeticModel.yNat n := Nat.le_floor hy2
    exact Real.log_pos (by exact_mod_cast (show 1 < ArithmeticModel.yNat n by omega))
  have hbudget : Real.log C + Scale.L n ≤
      5 * Real.log (ArithmeticModel.yNat n : ℝ) := by
    have hgapLower :
        Real.log (ArithmeticModel.y n) - Real.log 2 ≤
          Real.log (ArithmeticModel.yNat n : ℝ) := by
      linarith [hyGap.2]
    rw [ht] at hgapLower
    nlinarith
  let X : ℕ := ArithmeticModel.physicalBound C n / q
  by_cases hX : X = 0
  · simp [X, hX, hspos.le]
  · have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
    have hXleFloor : X ≤ ArithmeticModel.physicalBound C n :=
      Nat.div_le_self _ _
    have hfloorLe : (ArithmeticModel.physicalBound C n : ℝ) ≤
        C * (n : ℝ) := Nat.floor_le (by positivity)
    have hXle : (X : ℝ) ≤ C * (n : ℝ) :=
      (by exact_mod_cast hXleFloor : (X : ℝ) ≤
        (ArithmeticModel.physicalBound C n : ℝ)).trans hfloorLe
    have hlogX : Real.log (X : ℝ) ≤ Real.log (C * (n : ℝ)) :=
      Real.log_le_log hXpos hXle
    have hlogMul : Real.log (C * (n : ℝ)) =
        Real.log C + Scale.L n := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      rw [Real.log_mul hC.ne' hnR]
      rfl
    change Real.log (X : ℝ) ≤ _
    rw [hlogMul] at hlogX
    exact hlogX.trans hbudget

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/



private theorem reciprocalAF_isMultiplicative :
    reciprocalAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [reciprocalAF], ?_⟩
  intro m n hm hn hcop
  simp only [reciprocalAF, ArithmeticFunction.coe_mk, hm, hn,
    mul_ne_zero hm hn, if_false, Nat.cast_mul]
  field_simp

private theorem modulus_squarefree (P : Pattern) : Squarefree P.modulus := by
  unfold Pattern.modulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (P.prime_mem p hp) (P.prime_mem q hq)).mpr hpq)
  · intro p hp
    exact (P.prime_mem p hp).squarefree

/-- The exact identity
`sum_{a | M_H} mu(a)/a = phi(M_H)/M_H`, in the real field used by the
analytic estimates. -/
theorem sum_moebius_div_inv_eq_totient_ratio (P : Pattern) :
    (∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) =
      (P.modulus.totient : ℝ) / (P.modulus : ℝ) := by
  have hprod := reciprocalAF_isMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    reciprocalAF (modulus_squarefree P)
  have hprod' :
      (∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ))) =
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) := by
    calc
      _ = ∏ p ∈ P.modulus.primeFactors, (1 - reciprocalAF p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
        simp [reciprocalAF, hp0]
      _ = ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) * reciprocalAF a := hprod
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := (Nat.pos_of_mem_divisors ha).ne'
        simp [reciprocalAF, ha0, div_eq_mul_inv]
  have htotQ := Nat.totient_eq_mul_prod_factors P.modulus
  have htotR :
      (P.modulus.totient : ℝ) =
        (P.modulus : ℝ) *
          ∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) htotQ
    norm_num at hcast
    simpa [one_div] using hcast
  rw [← hprod']
  have hmod : (P.modulus : ℝ) ≠ 0 := by
    exact_mod_cast P.modulus_ne_zero
  apply (eq_div_iff hmod).2
  nlinarith





/-- Möbius closure including the forced head factor. -/
theorem head_moebius_coefficient_eq_density (P : Pattern) :
    (1 / (P.factor : ℝ)) *
        (∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) =
      headDensity P := by
  rw [sum_moebius_div_inv_eq_totient_ratio]
  rfl

/-! ## The common paper-scale main term -/





















/-- Once every endpoint has the same Dickman translate, the complete
Möbius sum is exactly the paper's head-density main term. -/
theorem common_endpoint_sum_eq_paperMarkedMain
    (P : Pattern) (A B R : ℝ) {n d : ℕ} (hd : 0 < d) :
    (∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) *
          ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) * R -
            (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) * R)) =
      headDensity P * ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
  have hfactor : (P.factor : ℝ) ≠ 0 := by
    exact_mod_cast P.factor_ne_zero
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = ((1 / (P.factor : ℝ)) *
          (∑ a ∈ P.modulus.divisors,
            (ArithmeticFunction.moebius a : ℝ) / (a : ℝ))) *
        ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have haR : (a : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
      norm_num only [Nat.cast_mul]
      field_simp [hfactor, haR, hdR]
    _ = headDensity P * ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
      rw [head_moebius_coefficient_eq_density]



theorem endpointCoefficient_nonneg (C : ℝ) (g : ℕ) :
    0 ≤ endpointCoefficient C g := by
  unfold endpointCoefficient
  positivity



theorem endpointFamilyCoefficient_nonneg (P : Pattern) {C : ℝ}
    (hC : 0 ≤ C) : 0 ≤ endpointFamilyCoefficient P C := by
  unfold endpointFamilyCoefficient
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg
      (mul_nonneg (endpointCoefficient_nonneg C (P.factor * a)) hC)
      (by positivity))





theorem headMoebiusMass_nonneg (P : Pattern) : 0 ≤ headMoebiusMass P := by
  unfold headMoebiusMass
  positivity

/-- The termwise error returned by the unconditional structured-cell
theorem is uniformly `O(n/(d log n))` on the complete four-mark range. -/
theorem raw_head_error_sum_le
    (P : Pattern) {A B K : ℝ} {n d : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hn : 1 < n) (hd : 0 < d)
    (hlogLower : (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ)) :
    (∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K *
            ((((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
              (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (yNat n : ℝ))) ≤
      (5 * K * (B + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * L n) := by
  have hL : 0 < L n := L_pos hn
  have hs : 0 < Real.log (yNat n : ℝ) :=
    (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlogLower
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hinvLog : 1 / Real.log (yNat n : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hs hL).2
    simpa only [one_mul] using (show L n ≤
      5 * Real.log (yNat n : ℝ) by linarith)
  have hterm (C : ℝ) (hC : 0 ≤ C) (a : ℕ)
      (ha : a ∈ P.modulus.divisors) :
      ((((physicalBound C n) / (P.factor * a * d) : ℕ) : ℝ)) ≤
        C * (n : ℝ) / (d : ℝ) := by
    have hfactor : 0 < P.factor := Nat.pos_of_ne_zero P.factor_ne_zero
    have haPos : 0 < a := Nat.pos_of_mem_divisors ha
    have hq : 0 < P.factor * a * d := by positivity
    have hcastDiv :
        ((((physicalBound C n) / (P.factor * a * d) : ℕ) : ℝ)) ≤
          (physicalBound C n : ℝ) /
            ((P.factor * a * d : ℕ) : ℝ) := Nat.cast_div_le
    have hfloor : (physicalBound C n : ℝ) ≤ C * (n : ℝ) :=
      Nat.floor_le (mul_nonneg hC (Nat.cast_nonneg n))
    have hden : (d : ℝ) ≤ ((P.factor * a * d : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul]
      have : (1 : ℝ) ≤ (P.factor : ℝ) * (a : ℝ) := by
        exact_mod_cast mul_pos hfactor haPos
      nlinarith [hdR]
    calc
      _ ≤ (physicalBound C n : ℝ) /
          ((P.factor * a * d : ℕ) : ℝ) := hcastDiv
      _ ≤ (C * (n : ℝ)) / ((P.factor * a * d : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right hfloor (by positivity)
      _ ≤ C * (n : ℝ) / (d : ℝ) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg hC (Nat.cast_nonneg n)) hdR hden
  calc
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K * (((B + A) * (n : ℝ) / (d : ℝ)) /
            Real.log (yNat n : ℝ))) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        K * ((((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
              (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (yNat n : ℝ) ≤
          (K * ((B + A) * (n : ℝ) / (d : ℝ))) /
            Real.log (yNat n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hs.le
          exact mul_le_mul_of_nonneg_left
            (by
              calc
                (((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
                    (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
                  B * (n : ℝ) / (d : ℝ) + A * (n : ℝ) / (d : ℝ) :=
                    add_le_add (hterm B hB a ha) (hterm A hA a ha)
                _ = (B + A) * (n : ℝ) / (d : ℝ) := by ring)
            hK
        _ = K * (((B + A) * (n : ℝ) / (d : ℝ)) /
            Real.log (yNat n : ℝ)) := by ring
    _ = headMoebiusMass P *
        (K * (((B + A) * (n : ℝ) / (d : ℝ)) /
          Real.log (yNat n : ℝ))) := by
      unfold headMoebiusMass
      rw [Finset.sum_mul]
    _ = (headMoebiusMass P * K * (B + A) * (n : ℝ) / (d : ℝ)) *
        (1 / Real.log (yNat n : ℝ)) := by ring
    _ ≤ (headMoebiusMass P * K * (B + A) * (n : ℝ) / (d : ℝ)) *
        (5 / L n) := by
      apply mul_le_mul_of_nonneg_left hinvLog
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (headMoebiusMass_nonneg P) hK) (add_nonneg hB hA))
          (Nat.cast_nonneg n))
        hdR.le
    _ = (5 * K * (B + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * L n) := by ring

/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PaperMovingPrefixMarkedCell -/
section


/-!
# Uniform moving-prefix endpoint bookkeeping

For a prefix endpoint `k` inside a fixed physical interval, put
`D = k / n`.  Then `physicalBound D n = k` exactly.  Moreover `D` stays
in the original fixed compact physical interval.  These elementary facts
allow the marked-cell endpoint theorem to be applied without pretending
that the moving endpoint is fixed as `n` varies.
-/

namespace Erdos390.Full.PaperMovingPrefixMarkedCell

open ArithmeticModel PaperScaleMarkedCell
open HeadPattern StructuredCells MarkedFriableAsymptotic
open StructuredCellAsymptotic
open scoped BigOperators

noncomputable section







/-- A prefix strictly above `floor(A n)` has scale strictly above `A`. -/
theorem lt_prefixScale_of_physicalBound_lt
    {A : ℝ} {n k : ℕ} (hn : 0 < n)
    (hk : physicalBound A n < k) :
    A < prefixScale n k := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfloor : A * (n : ℝ) < (physicalBound A n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (A * (n : ℝ))
  have hkCast : (physicalBound A n : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hk
  apply (lt_div_iff₀ hnR).2
  exact hfloor.trans_le hkCast

/-- A prefix below `floor(C n)` has scale at most `C`. -/
theorem prefixScale_le_of_le_physicalBound
    {C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hk : k ≤ physicalBound C n) :
    prefixScale n k ≤ C := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkFloor : (k : ℝ) ≤ (physicalBound C n : ℝ) := by
    exact_mod_cast hk
  have hfloor : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hC hnR.le)
  apply (div_le_iff₀ hnR).2
  exact hkFloor.trans hfloor

/-- Combined compact containment for every moving prefix used by Abel
summation. -/
theorem prefixScale_mem_compact
    {A C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hlow : physicalBound A n < k)
    (hhigh : k ≤ physicalBound C n) :
    A < prefixScale n k ∧ prefixScale n k ≤ C :=
  ⟨lt_prefixScale_of_physicalBound_lt hn hlow,
    prefixScale_le_of_le_physicalBound hC hn hhigh⟩



theorem endpointCoefficient_le_compactEndpointCoefficient
    {A C D : ℝ} (g : ℕ) (hA : 0 < A)
    (hAD : A ≤ D) (hDC : D ≤ C) :
    endpointCoefficient D g ≤ compactEndpointCoefficient A C g := by
  have hD : 0 < D := hA.trans_le hAD
  have hC : 0 < C := hD.trans_le hDC
  have hlogAD : Real.log A ≤ Real.log D :=
    Real.log_le_log hA hAD
  have hlogDC : Real.log D ≤ Real.log C :=
    Real.log_le_log hD hDC
  have hlogDabs : |Real.log D| ≤ |Real.log A| + |Real.log C| := by
    rw [abs_le]
    constructor
    · calc
        -(|Real.log A| + |Real.log C|) ≤ -|Real.log A| := by
          linarith [abs_nonneg (Real.log C)]
        _ ≤ Real.log A := neg_abs_le (Real.log A)
        _ ≤ Real.log D := hlogAD
    · calc
        Real.log D ≤ Real.log C := hlogDC
        _ ≤ |Real.log C| := le_abs_self (Real.log C)
        _ ≤ |Real.log A| + |Real.log C| := by
          linarith [abs_nonneg (Real.log A)]
  have hdiff : |Real.log D - Real.log (g : ℝ)| ≤
      |Real.log A| + |Real.log C| + |Real.log (g : ℝ)| := by
    calc
      |Real.log D - Real.log (g : ℝ)| ≤
          |Real.log D| + |Real.log (g : ℝ)| := abs_sub _ _
      _ ≤ (|Real.log A| + |Real.log C|) +
          |Real.log (g : ℝ)| := by linarith
  unfold endpointCoefficient compactEndpointCoefficient
  linarith

theorem compactEndpointCoefficient_nonneg (A C : ℝ) (g : ℕ) :
    0 ≤ compactEndpointCoefficient A C g := by
  unfold compactEndpointCoefficient
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity



theorem compactEndpointFamilyCoefficient_nonneg
    (P : HeadPattern.Pattern) {A C : ℝ} (hC : 0 ≤ C) :
    0 ≤ compactEndpointFamilyCoefficient P A C := by
  unfold compactEndpointFamilyCoefficient
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg
      (mul_nonneg (compactEndpointCoefficient_nonneg A C _) hC)
      (by positivity))

theorem endpointFamilyCoefficient_le_compact
    (P : HeadPattern.Pattern) {A C D : ℝ}
    (hA : 0 < A) (hAD : A ≤ D) (hDC : D ≤ C) :
    endpointFamilyCoefficient P D ≤
      compactEndpointFamilyCoefficient P A C := by
  have hD : 0 < D := hA.trans_le hAD
  have hC : 0 < C := hD.trans_le hDC
  unfold endpointFamilyCoefficient compactEndpointFamilyCoefficient
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hcoef := endpointCoefficient_le_compactEndpointCoefficient
    (A := A) (C := C) (D := D) (P.factor * a) hA hAD hDC
  have hcoef0 := endpointCoefficient_nonneg D (P.factor * a)
  have hcompact0 := compactEndpointCoefficient_nonneg A C (P.factor * a)
  have hden : (0 : ℝ) < ((P.factor * a : ℕ) : ℝ) := by
    exact_mod_cast mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
      (Nat.pos_of_mem_divisors ha)
  calc
    endpointCoefficient D (P.factor * a) * D /
        ((P.factor * a : ℕ) : ℝ) ≤
      compactEndpointCoefficient A C (P.factor * a) * D /
        ((P.factor * a : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hD.le) hden.le
    _ ≤ compactEndpointCoefficient A C (P.factor * a) * C /
        ((P.factor * a : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDC hcompact0) hden.le

/-- The paper-scale marked count, uniformly in every integer upper prefix
inside one fixed physical interval.  The common main term is evaluated at
the exact moving scale `k/n`; the error constant and threshold do not depend
on `k`. -/
theorem exists_uniform_movingUpper_markedCell_paper_main_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      |((markedCell P (physicalBound A n) k (yNat n) d).card : ℝ) -
          paperMarkedMain P A (prefixScale n k) n d| ≤
        K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by
  obtain ⟨Kraw, hKraw, Y₀, hraw⟩ :=
    exists_uniform_markedCell_dickman_sum_bound
  obtain ⟨NmarginA, hmarginA₀⟩ := exists_endpoint_margin_threshold P hA
  obtain ⟨NlogA, hlogA₀⟩ := exists_physicalBound_log_range hA
  obtain ⟨NlogC, hlogC₀⟩ :=
    exists_physicalBound_log_range (hA.trans hAC)
  let H : ℕ := max Y₀ (max P.modulus 2)
  have hyTop : Filter.Tendsto (fun n : ℕ => ArithmeticModel.y n)
      Filter.atTop Filter.atTop := by
    simpa [ArithmeticModel.y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hyEvent : ∀ᶠ n : ℕ in Filter.atTop, (H : ℝ) ≤ y n :=
    hyTop.eventually (Filter.eventually_ge_atTop (H : ℝ))
  have hlogEvent := FriableAsymptotic.eventually_one_fifth_L_le_log_yNat
  have hscaleAll : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (H : ℝ) ≤ y n ∧
        (1 / 5 : ℝ) * Scale.L n ≤ Real.log (yNat n : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hyEvent, hlogEvent] with
      n hn hy hlog
    exact ⟨hn, hy, hlog⟩
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleAll
  let N₀ := max NmarginA (max NlogA (max NlogC Nscale))
  let K : ℝ :=
    1 + 5 * Kraw * (C + A) * headMoebiusMass P +
      compactEndpointFamilyCoefficient P A C +
      endpointFamilyCoefficient P A
  have hC : 0 < C := hA.trans hAC
  have hrawCoeff0 :
      0 ≤ 5 * Kraw * (C + A) * headMoebiusMass P := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hKraw.le) (add_nonneg hC.le hA.le))
      (headMoebiusMass_nonneg P)
  have hcompactCoeff0 :
      0 ≤ compactEndpointFamilyCoefficient P A C :=
    compactEndpointFamilyCoefficient_nonneg P hC.le
  have hAcoeff0 : 0 ≤ endpointFamilyCoefficient P A :=
    endpointFamilyCoefficient_nonneg P hA.le
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, N₀, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  have hNmA : NmarginA ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNlA : NlogA ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNlC : NlogC ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNs : Nscale ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hyH, hlogLower⟩ := hNscale n hNs
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  have hDcompact := prefixScale_mem_compact hC.le hnpos hlow hhigh
  let D : ℝ := prefixScale n k
  have hAD : A ≤ D := by
    exact (by simpa only [D] using hDcompact.1.le)
  have hDC : D ≤ C := by
    simpa only [D] using hDcompact.2
  have hD : 0 < D := hA.trans_le hAD
  have hDend : physicalBound D n = k := by
    simpa only [D] using physicalBound_prefixScale_eq hnpos
  have hHy : H ≤ yNat n := Nat.le_floor hyH
  have hY₀ : Y₀ ≤ yNat n :=
    (le_max_left Y₀ (max P.modulus 2)).trans hHy
  have hmodY : P.modulus ≤ yNat n :=
    (le_max_left P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hyNat2 : 2 ≤ yNat n :=
    (le_max_right P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hy2 : (2 : ℝ) ≤ y n := by
    exact (by exact_mod_cast hyNat2 : (2 : ℝ) ≤ (yNat n : ℝ)).trans
      (Nat.floor_le (Scale.y_pos hnpos).le)
  have hhead : ∀ p ∈ P.primes, p ≤ yNat n := by
    intro p hp
    have hpDvd : p ∣ P.modulus := by
      unfold Pattern.modulus
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero P.modulus_ne_zero) hpDvd).trans
      hmodY
  have hlohi : physicalBound A n ≤ physicalBound D n := by
    rw [hDend]
    exact hlow.le
  have hmarginA : ∀ a ∈ P.modulus.divisors,
      4 ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      Scale.L n ≤ A * (n : ℝ) /
        ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    exact hmarginA₀ hNmA ha hd hd4
  have hmarginD : ∀ a ∈ P.modulus.divisors,
      4 ≤ D * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      Scale.L n ≤ D * (n : ℝ) /
        ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    have hden : (0 : ℝ) ≤ ((P.factor * a * d : ℕ) : ℝ) := by positivity
    have hnum : A * (n : ℝ) ≤ D * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hAD (by positivity)
    have hratio : A * (n : ℝ) /
          ((P.factor * a * d : ℕ) : ℝ) ≤
        D * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum hden
    exact ⟨(hmarginA a ha).1.trans hratio,
      (hmarginA a ha).2.trans hratio⟩
  have hlogA : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    exact hlogA₀ hNlA (mul_pos
      (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
        (Nat.pos_of_mem_divisors ha)) hd)
  have hlogD : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound D n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    let q : ℕ := P.factor * a * d
    have hq : 0 < q := by
      dsimp only [q]
      exact mul_pos
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd
    have hlogC := hlogC₀ hNlC hq
    have hquot : physicalBound D n / q ≤ physicalBound C n / q := by
      apply Nat.div_le_div_right
      rw [hDend]
      exact hhigh
    by_cases hz : physicalBound D n / q = 0
    · rw [hz]
      have hylog0 : 0 ≤ Real.log (yNat n : ℝ) := by
        exact (by positivity : 0 < (1 / 5 : ℝ) * Scale.L n).le.trans
          hlogLower
      simpa only [Nat.cast_zero, Real.log_zero] using
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hylog0)
    · have hleft : (0 : ℝ) < ((physicalBound D n / q : ℕ) : ℝ) := by
        positivity
      have hlogMono :
          Real.log ((physicalBound D n / q : ℕ) : ℝ) ≤
            Real.log ((physicalBound C n / q : ℕ) : ℝ) := by
        exact Real.log_le_log hleft (by exact_mod_cast hquot)
      exact hlogMono.trans hlogC
  have hraw₀ := hraw P hY₀ hlohi hhead hd hdsmooth hcop hlogA hlogD
  have hraw₁ :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a| ≤
      (5 * Kraw * (D + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) :=
    hraw₀.trans
      (raw_head_error_sum_le P hA.le hD.le hKraw.le hn hd hlogLower)
  have hscale : 0 ≤ (n : ℝ) / ((d : ℝ) * Scale.L n) := by positivity
  have hraw₁u :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a| ≤
      (5 * Kraw * (C + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    refine hraw₁.trans ?_
    rw [show
      (5 * Kraw * (D + A) * headMoebiusMass P) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (5 * Kraw * (D + A) * headMoebiusMass P) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    rw [show
      (5 * Kraw * (C + A) * headMoebiusMass P) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (5 * Kraw * (C + A) * headMoebiusMass P) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    apply mul_le_mul_of_nonneg_right _ hscale
    have hmass0 := headMoebiusMass_nonneg P
    nlinarith
  have hcommon := headDivisorMain_sum_sub_common_le P hA hD hn hd hd4
    hy2 hlogLower hmarginA hmarginD hlogA hlogD
  have hcollapse := common_endpoint_sum_eq_paperMarkedMain P A D
    (DickmanBasic.rho (paperDivisorCoordinate n d)) (n := n) (d := d) hd
  have hcommon' :
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a) - paperMarkedMain P A D n d| ≤
        (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    unfold paperMarkedMain
    rw [← hcollapse]
    exact hcommon
  have hfamilyD : endpointFamilyCoefficient P D ≤
      compactEndpointFamilyCoefficient P A C :=
    endpointFamilyCoefficient_le_compact P hA hAD hDC
  have hcommonU :
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a) - paperMarkedMain P A D n d| ≤
        (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    refine hcommon'.trans ?_
    rw [show
      (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * Scale.L n) =
        (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    rw [show
      (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    apply mul_le_mul_of_nonneg_right _ hscale
    linarith
  have htotal :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) - paperMarkedMain P A D n d| ≤
        K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    calc
      _ ≤
        |((markedCell P (physicalBound A n) (physicalBound D n)
              (yNat n) d).card : ℝ) -
          ∑ a ∈ P.modulus.divisors,
            headDivisorMain P (physicalBound A n) (physicalBound D n)
              (yNat n) d a| +
        |(∑ a ∈ P.modulus.divisors,
            headDivisorMain P (physicalBound A n) (physicalBound D n)
              (yNat n) d a) - paperMarkedMain P A D n d| :=
          abs_sub_le _ _ _
      _ ≤ (5 * Kraw * (C + A) * headMoebiusMass P) *
            (n : ℝ) / ((d : ℝ) * Scale.L n) +
          (compactEndpointFamilyCoefficient P A C +
            endpointFamilyCoefficient P A) *
            (n : ℝ) / ((d : ℝ) * Scale.L n) :=
        add_le_add hraw₁u hcommonU
      _ = (5 * Kraw * (C + A) * headMoebiusMass P +
            compactEndpointFamilyCoefficient P A C +
            endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) := by ring
      _ ≤ K * ((n : ℝ) / ((d : ℝ) * Scale.L n)) := by
        apply mul_le_mul_of_nonneg_right _ hscale
        dsimp only [K]
        linarith
      _ = K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by ring
  simpa only [D, hDend] using htotal

/-! ## Exact prefix normalization identities -/





















end

end Erdos390.Full.PaperMovingPrefixMarkedCell

end

theorem solution :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      ∃ K,
        And (LT.lt.{0} (0 : Real) K)
          (∃ N₀,
            ∀ {n k d : Nat},
              LE.le.{0} N₀ n →
                LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                  LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                    LT.lt.{0} (0 : Nat) d →
                      LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                        Membership.mem.{0, 0}
                            (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat)))
                            d →
                          Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (↑(Finset.card.{0}
                                      (Erdos390.Full.StructuredCells.markedCell P
                                        (Erdos390.Full.ArithmeticModel.physicalBound A n) k
                                        (Erdos390.Full.ArithmeticModel.yNat n) d)))
                                  (Erdos390.Full.PaperScaleMarkedCell.paperMarkedMain P A
                                    (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixScale n k) n d)))
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K ↑n)
                                (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n)))) := by
  exact @Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingUpper_markedCell_paper_main_bound
