-- Prove2me | solution 1 for WeakGoldbach.prime_power_part_le_above_2e18
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T03:54:02.730037+00:00
-- url     : https://prove2.me/submissions/7a622ca0-f10d-46b8-98d8-71866288b209

import Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one

open Finset ArithmeticFunction

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∑ t ∈ (Finset.range (m - 1)).filter
        (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))),
      (ArithmeticFunction.vonMangoldt (m - t) : ℝ)
        * (ArithmeticFunction.vonMangoldt (m + t) : ℝ)
      ≤ (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
          * (m : ℝ) * (1 / 10) := by
  classical
  set s := Finset.range (m - 1) with hsdef
  set L := Real.log (2 * m) with hLdef
  set ppS : Finset ℕ := (Finset.range (2 * m + 1)).filter
    (fun x => IsPrimePow x ∧ ¬ x.Prime) with hppSdef
  set f : ℕ → ℝ := fun t =>
    (vonMangoldt (m - t) : ℝ) * (vonMangoldt (m + t) : ℝ) with hfdef
  set B : Finset ℕ := s.filter
    (fun t => f t ≠ 0 ∧ ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))) with hBdef
  -- the filtered sum equals the sum over the support B
  have hsumB : ∑ t ∈ s.filter (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))), f t
      = ∑ t ∈ B, f t := by
    symm
    apply Finset.sum_subset
    · intro t ht
      have h := Finset.mem_filter.mp (hBdef ▸ ht)
      exact Finset.mem_filter.mpr ⟨h.1, h.2.2⟩
    · intro t htf htnotin
      have hmem := Finset.mem_filter.mp htf
      by_contra hne
      exact htnotin (hBdef ▸ Finset.mem_filter.mpr ⟨hmem.1, hne, hmem.2⟩)
  -- per-term bound
  have hL0 : (0 : ℝ) ≤ L :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * m))
  have hterm : ∀ t ∈ B, f t ≤ L ^ 2 := by
    intro t ht
    rw [hBdef, Finset.mem_filter] at ht
    have htm : t ≤ m - 2 := by
      have := Finset.mem_range.mp ht.1; omega
    have h1 : (vonMangoldt (m - t) : ℝ) ≤ L :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < m - t))
          (by exact_mod_cast (by omega : m - t ≤ 2 * m)))
    have h2 : (vonMangoldt (m + t) : ℝ) ≤ L :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < m + t))
          (by exact_mod_cast (by omega : m + t ≤ 2 * m)))
    have h3 : (0 : ℝ) ≤ vonMangoldt (m + t) := ArithmeticFunction.vonMangoldt_nonneg
    calc f t = (vonMangoldt (m - t) : ℝ) * (vonMangoldt (m + t) : ℝ) := rfl
      _ ≤ L * L := mul_le_mul h1 h2 h3 hL0
      _ = L ^ 2 := by ring
  have hsumL : ∑ t ∈ B, f t ≤ B.card * L ^ 2 := by
    calc ∑ t ∈ B, f t ≤ ∑ _ ∈ B, L ^ 2 := Finset.sum_le_sum hterm
      _ = B.card * L ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- B ⊆ T₁ ∪ T₂
  set T₁ : Finset ℕ := s.filter (fun t => m - t ∈ ppS) with hT1def
  set T₂ : Finset ℕ := s.filter (fun t => m + t ∈ ppS) with hT2def
  have hBpp : ∀ t ∈ B, m - t ∈ ppS ∨ m + t ∈ ppS := by
    intro t ht
    rw [hBdef, Finset.mem_filter] at ht
    obtain ⟨hts, hne, hnotboth⟩ := ht
    have htm : t ≤ m - 2 := by
      have := Finset.mem_range.mp hts; omega
    have hΛ : (vonMangoldt (m - t) : ℝ) ≠ 0 ∧ (vonMangoldt (m + t) : ℝ) ≠ 0 :=
      mul_ne_zero_iff.mp hne
    have hpp1 : IsPrimePow (m - t) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ.1
    have hpp2 : IsPrimePow (m + t) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ.2
    rcases (not_and_or.mp hnotboth) with hnp1 | hnp2
    · left
      rw [hppSdef, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hpp1, hnp1⟩
    · right
      rw [hppSdef, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hpp2, hnp2⟩
  have hBT : B ⊆ T₁ ∪ T₂ := by
    intro t ht
    have htm : t ∈ s := by
      rw [hBdef, Finset.mem_filter] at ht; exact ht.1
    rw [Finset.mem_union, hT1def, hT2def]
    rcases hBpp t ht with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨htm, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨htm, h⟩)
  have hcardT1 : T₁.card ≤ ppS.card := by
    apply Finset.card_le_card_of_injOn (fun t => m - t)
    · intro t ht
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    · intro t₁ h1 t₂ h2 heq
      have i1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).1
      have i2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).1
      have heq' : m - t₁ = m - t₂ := heq
      omega
  have hcardT2 : T₂.card ≤ ppS.card := by
    apply Finset.card_le_card_of_injOn (fun t => m + t)
    · intro t ht
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    · intro t₁ _ t₂ _ heq
      have heq' : m + t₁ = m + t₂ := heq
      omega
  have hBcard : B.card ≤ 2 * ppS.card := by
    calc B.card ≤ (T₁ ∪ T₂).card := Finset.card_le_card hBT
      _ ≤ T₁.card + T₂.card := Finset.card_union_le _ _
      _ ≤ ppS.card + ppS.card := Nat.add_le_add hcardT1 hcardT2
      _ = 2 * ppS.card := by ring
  -- count proper prime powers via the (minFac, exponent) injection
  have hN : ppS.card ≤ (Nat.sqrt (2 * m) + 1) * (Nat.log 2 (2 * m) + 1) := by
    rw [← Finset.card_range (Nat.sqrt (2 * m) + 1),
      ← Finset.card_range (Nat.log 2 (2 * m) + 1), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun x => (x.minFac, x.factorization x.minFac))
    · intro x hx
      obtain ⟨hxr, hpp, hnp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hxm : x ≤ 2 * m := by
        have := Finset.mem_range.mp hxr; omega
      have hxpos : 0 < x := hpp.pos
      have hxne1 : x ≠ 1 := fun h1 => not_isPrimePow_one (h1 ▸ hpp)
      have hminp : x.minFac.Prime := Nat.minFac_prime hxne1
      have hmin2 : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self hxpos hnp
      have hfact_eq : x.minFac ^ x.factorization x.minFac = x :=
        hpp.minFac_pow_factorization_eq
      have hminfac_le : x.minFac ≤ Nat.sqrt (2 * m) := by
        rw [Nat.le_sqrt]
        calc x.minFac * x.minFac = x.minFac ^ 2 := by ring
          _ ≤ x := hmin2
          _ ≤ 2 * m := hxm
      have h2e : 2 ^ x.factorization x.minFac ≤ 2 * m := by
        calc 2 ^ x.factorization x.minFac
            ≤ x.minFac ^ x.factorization x.minFac :=
              Nat.pow_le_pow_left (Nat.Prime.two_le hminp) _
          _ = x := hfact_eq
          _ ≤ 2 * m := hxm
      have hele : x.factorization x.minFac ≤ Nat.log 2 (2 * m) :=
        Nat.le_log_of_pow_le (by norm_num) h2e
      apply Finset.mem_coe.mpr
      rw [Finset.mem_product]
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hminfac_le),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hele)⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      have hx₁' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₁)
      have hx₂' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₂)
      have e1 : x₁.minFac ^ x₁.factorization x₁.minFac = x₁ :=
        hx₁'.2.1.minFac_pow_factorization_eq
      have e2 : x₂.minFac ^ x₂.factorization x₂.minFac = x₂ :=
        hx₂'.2.1.minFac_pow_factorization_eq
      have hmf : x₁.minFac = x₂.minFac := congrArg Prod.fst heq
      have hexp : x₁.factorization x₁.minFac = x₂.factorization x₂.minFac :=
        congrArg Prod.snd heq
      rw [hmf] at hexp
      calc x₁ = x₁.minFac ^ x₁.factorization x₁.minFac := e1.symm
        _ = x₂.minFac ^ x₂.factorization x₂.minFac := by rw [hmf, hexp]
        _ = x₂ := e2
  -- real bounds
  have hxpos : (0 : ℝ) < 2 * m := by exact_mod_cast (by omega : 0 < 2 * m)
  set y : ℝ := (2 * m : ℝ) ^ ((1 : ℝ) / 6) with hydef
  have hypos : (0 : ℝ) < y := Real.rpow_pos_of_pos hxpos _
  have hy1130 : (1130 : ℝ) ≤ y := by
    have h1 : ((1130 : ℝ) ^ (6 : ℕ)) ≤ 2 * m := by
      have h6 : (1130 : ℕ) ^ 6 ≤ 2 * m := by norm_num; omega
      exact_mod_cast h6
    calc (1130 : ℝ) = ((1130 : ℝ) ^ (6 : ℕ)) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1130)]
          rw [show (((6 : ℕ) : ℝ)) * (1 / 6) = 1 by norm_num, Real.rpow_one]
      _ ≤ y := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hy6 : y ^ (6 : ℕ) = 2 * m := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    rw [show (1 / 6 : ℝ) * (((6 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
  have hlogx : L = 6 * Real.log y := by
    rw [hLdef, ← hy6, ← Real.rpow_natCast, Real.log_rpow hypos]
    ring
  have hlogy : Real.log y ≤ 3 * (y ^ ((1 : ℝ) / 3) - 1) := by
    have h1 : Real.log (y ^ ((1 : ℝ) / 3)) ≤ y ^ ((1 : ℝ) / 3) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hypos _)
    have h2 : Real.log (y ^ ((1 : ℝ) / 3)) = (1 / 3) * Real.log y :=
      Real.log_rpow hypos _
    linarith
  have h108 : (108 : ℝ) * y ^ ((1 : ℝ) / 3) ≤ y := by
    have h23 : (108 : ℝ) ≤ y ^ ((2 : ℝ) / 3) := by
      have h1130 : (108 : ℝ) ≤ (1130 : ℝ) ^ ((2 : ℝ) / 3) := by
        by_contra hneg
        push_neg at hneg
        have hlt : ((1130 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) < (108 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hneg (Real.rpow_nonneg (by norm_num) _) three_ne_zero
        have heq : ((1130 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (1130 : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1130)]
          rw [show ((2 : ℝ) / 3) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [heq] at hlt
        norm_num at hlt
      exact le_trans h1130 (Real.rpow_le_rpow (by norm_num) hy1130 (by norm_num))
    have hmul : y ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) = y := by
      rw [← Real.rpow_add hypos, show ((2 : ℝ) / 3) + (1 / 3) = 1 by norm_num,
        Real.rpow_one]
    calc (108 : ℝ) * y ^ ((1 : ℝ) / 3) ≤ y ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right h23 (Real.rpow_nonneg hypos.le _)
      _ = y := hmul
  have hLle : L ≤ y / 6 := by
    have h := hlogy
    rw [hlogx]
    nlinarith [h108]
  have hLsq : L ^ 2 ≤ (y / 6) ^ 2 := by
    have hy6pos : (0 : ℝ) ≤ y / 6 := by linarith [hypos]
    calc L ^ 2 = L * L := sq _
      _ ≤ (y / 6) * (y / 6) := mul_le_mul hLle hLle hL0 hy6pos
      _ = (y / 6) ^ 2 := (sq _).symm
  have hsqrt : (Nat.sqrt (2 * m) : ℝ) ≤ Real.sqrt (2 * m) := by
    apply Real.le_sqrt_of_sq_le
    have hsq : Nat.sqrt (2 * m) * Nat.sqrt (2 * m) ≤ 2 * m := Nat.sqrt_le (2 * m)
    calc ((Nat.sqrt (2 * m) : ℝ)) ^ 2
        = ((Nat.sqrt (2 * m) * Nat.sqrt (2 * m) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 * m : ℝ) := by exact_mod_cast hsq
  have hsqrt2 : (Nat.sqrt (2 * m) : ℝ) + 1 ≤ 2 * Real.sqrt (2 * m) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (2 * m) := by
      apply Real.le_sqrt_of_sq_le
      norm_num
      exact_mod_cast (by omega : (1 : ℕ) ^ 2 ≤ 2 * m)
    linarith [hsqrt]
  have hnatlog : (Nat.log 2 (2 * m) : ℝ) * Real.log 2 ≤ L := by
    have hp : ((2 : ℝ) ^ (Nat.log 2 (2 * m))) ≤ (2 * m : ℝ) := by
      have h := Nat.pow_log_le_self 2 (by omega : 2 * m ≠ 0)
      calc (2 : ℝ) ^ (Nat.log 2 (2 * m))
          = (((2 : ℕ) ^ (Nat.log 2 (2 * m)) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (2 * m : ℝ) := by exact_mod_cast h
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 (2 * m)) := by positivity
    have hl := Real.log_le_log hpos2 hp
    rw [Real.log_pow, ← hLdef] at hl
    exact hl
  have hlog2ge : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : (Nat.log 2 (2 * m) : ℝ) + 1 ≤ y / 4 := by
    have hdiv : (Nat.log 2 (2 * m) : ℝ) ≤ L / Real.log 2 :=
      (le_div_iff₀ hlog2pos).mpr hnatlog
    have h4 : L / Real.log 2 ≤ y / 4 - 1 := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hLle, hlog2ge, hy1130]
    linarith
  -- assemble
  have hBcard_r : (B.card : ℝ) ≤ 2 * (((Nat.sqrt (2 * m) + 1) * (Nat.log 2 (2 * m) + 1) : ℕ) : ℝ) := by
    have := Nat.le_trans hBcard (Nat.mul_le_mul_left 2 hN)
    exact_mod_cast this
  have hS : 1 ≤ ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    WeakGoldbach.singular_series_factor_ge_one (2 * m)
  have hy3 : y ^ (3 : ℕ) = Real.sqrt (2 * m) := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    rw [show (1 / 6 : ℝ) * ((3 : ℕ) : ℝ) = 1 / 2 by norm_num]
    rw [Real.sqrt_eq_rpow]
  have hprod : (B.card : ℝ) * L ^ 2 ≤ (2 * m : ℝ) / 36 := by
    have hAB : ((Nat.sqrt (2 * m) : ℝ) + 1) * ((Nat.log 2 (2 * m) : ℝ) + 1)
        ≤ (2 * Real.sqrt (2 * m)) * (y / 4) :=
      mul_le_mul hsqrt2 hlogb
        (add_nonneg (by positivity) zero_le_one)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    have hAB' : (0 : ℝ) ≤ (2 * Real.sqrt (2 * m)) * (y / 4) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (div_nonneg hypos.le (by norm_num))
    have hABC : ((Nat.sqrt (2 * m) : ℝ) + 1) * ((Nat.log 2 (2 * m) : ℝ) + 1) * L ^ 2
        ≤ (2 * Real.sqrt (2 * m)) * (y / 4) * (y / 6) ^ 2 :=
      mul_le_mul hAB hLsq (sq_nonneg L) hAB'
    calc (B.card : ℝ) * L ^ 2
        ≤ (2 * (((Nat.sqrt (2 * m) + 1) * (Nat.log 2 (2 * m) + 1) : ℕ) : ℝ)) * L ^ 2 :=
          mul_le_mul_of_nonneg_right hBcard_r (sq_nonneg L)
      _ = 2 * (((Nat.sqrt (2 * m) : ℝ) + 1) * ((Nat.log 2 (2 * m) : ℝ) + 1) * L ^ 2) := by
          push_cast; ring
      _ ≤ 2 * ((2 * Real.sqrt (2 * m)) * (y / 4) * (y / 6) ^ 2) :=
          mul_le_mul_of_nonneg_left hABC (by norm_num : (0 : ℝ) ≤ 2)
      _ = (Real.sqrt (2 * m)) * (y ^ (3 : ℕ)) / 36 := by ring
      _ = (2 * m : ℝ) / 36 := by
          rw [hy3, ← pow_two, Real.sq_sqrt hxpos.le]
  calc ∑ t ∈ s.filter (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))), f t
      = ∑ t ∈ B, f t := hsumB
    _ ≤ B.card * L ^ 2 := hsumL
    _ ≤ (2 * m : ℝ) / 36 := hprod
    _ = (m : ℝ) / 18 := by ring
    _ ≤ (m : ℝ) / 10 := by
        have hm0 : (0 : ℝ) ≤ m := by positivity
        linarith [hm0]
    _ ≤ (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
          * (m : ℝ) * (1 / 10) := by
        have hmpos : (0 : ℝ) ≤ (m : ℝ) / 10 := by positivity
        calc (m : ℝ) / 10 = 1 * ((m : ℝ) / 10) := by ring
          _ ≤ (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
              * ((m : ℝ) / 10) :=
              mul_le_mul_of_nonneg_right hS hmpos
          _ = _ := by ring
