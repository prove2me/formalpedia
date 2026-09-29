-- Prove2me | solution 1 for mme_stothers_general_profile_rate_below_marginal_multinomial
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T04:57:54.893812+00:00
-- url     : https://prove2.me/submissions/c53a51e2-c4dd-4e58-ba34-0becaccbe368

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth.GeneralProfileRate

private theorem exp_log_two_entropyBits_eq_prod_rpow
    {Dt : Type*} [Fintype Dt]
    (p : Dt → ℝ) (hp : ∀ i, 0 < p i) :
    Real.exp (Real.log 2 * mme_modern_entropyBits p) =
      ∏ i, Real.rpow (p i) (-p i) := by
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [show Real.log 2 * mme_modern_entropyBits p =
      ∑ i, -(p i * Real.log (p i)) by
    unfold mme_modern_entropyBits
    rw [mul_div_cancel₀ _ hlog2]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.negMulLog_def]
    ring]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [show Real.rpow (p i) (-p i) =
      Real.exp (Real.log (p i) * (-p i)) from
    Real.rpow_def_of_pos (hp i) (-p i)]
  congr 1
  ring

/-! ### Elementary facts about an integral ten-class profile -/

private theorem scale_pos (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    0 < ∑ r : Fin 10, classMultiplicity r * base r := by
  refine Finset.sum_pos' (fun i _ ↦ Nat.zero_le _) ⟨0, Finset.mem_univ 0, ?_⟩
  have := hbase 0
  simpa [classMultiplicity] using this

private theorem baseReal_pos (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (i : Fin 10) : (0 : ℝ) < (base i : ℝ) := by
  exact_mod_cast hbase i

private theorem Q_smul (base : Fin 10 → ℕ) (c : ℝ) (j : Fin 9) :
    Q (fun i ↦ (base i : ℝ) / c) j = Q (fun i ↦ (base i : ℝ)) j / c := by
  fin_cases j <;> simp [Q] <;> ring

private theorem marg_real_pos (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (j : Fin 9) : (0 : ℝ) < Q (fun i ↦ (base i : ℝ)) j := by
  have h0 := baseReal_pos base hbase 0
  have h1 := baseReal_pos base hbase 1
  have h2 := baseReal_pos base hbase 2
  have h3 := baseReal_pos base hbase 3
  have h4 := baseReal_pos base hbase 4
  have h5 := baseReal_pos base hbase 5
  have h6 := baseReal_pos base hbase 6
  have h7 := baseReal_pos base hbase 7
  have h8 := baseReal_pos base hbase 8
  have h9 := baseReal_pos base hbase 9
  have n0 := hbase 0
  have n1 := hbase 1
  have n2 := hbase 2
  have n3 := hbase 3
  have n4 := hbase 4
  have n5 := hbase 5
  have n6 := hbase 6
  have n7 := hbase 7
  have n8 := hbase 8
  have n9 := hbase 9
  fin_cases j <;> simp [Q] <;> linarith

private theorem Q_sum (base : Fin 10 → ℕ) :
    ∑ j : Fin 9, Q (fun i ↦ (base i : ℝ)) j =
      3 * ∑ r : Fin 10, ((classMultiplicity r : ℝ) * (base r : ℝ)) := by
  simp [Q, classMultiplicity, Fin.sum_univ_succ]
  ring

private theorem classValue_pos (tau : ℝ) (i : Fin 10) :
    0 < classValue 6 tau i := by
  fin_cases i <;>
    simp [classValue, E, H, L] <;> positivity

end MME.StothersFourth.GeneralProfileRate

namespace MME.StothersFourth.GeneralProfileRate

private noncomputable def margProfile (marg : Fin 9 → ℕ) (D : ℕ) (j : Fin 9) : ℝ :=
  (marg j : ℝ) / ((3 * D : ℕ) : ℝ)

private noncomputable def marginalRate (marg : Fin 9 → ℕ) (D : ℕ) : ℝ :=
  ∏ j : Fin 9, Real.rpow (margProfile marg D j) (-margProfile marg D j)

private noncomputable def capacityInner
    (tau : ℝ) (base : Fin 10 → ℕ) (m : ℕ) : ℝ :=
  ∏ r : Fin 10,
    (classValue 6 tau r) ^ (classMultiplicity r * (base r * m))

private theorem marg_pos (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ)
    (hbase : ∀ r, 0 < base r)
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j)
    (j : Fin 9) : 0 < marg j := by
  have h : (0 : ℝ) < (marg j : ℝ) := by
    rw [hmarg j]; exact marg_real_pos base hbase j
  exact_mod_cast h

private theorem marg_sum (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hD : D = ∑ r : Fin 10, classMultiplicity r * base r)
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j) :
    ∑ j : Fin 9, marg j = 3 * D := by
  have hreal : ((∑ j : Fin 9, marg j : ℕ) : ℝ) = ((3 * D : ℕ) : ℝ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) ↦ hmarg j), Q_sum, hD]
    push_cast
    ring
  exact_mod_cast hreal

private theorem margProfile_pos (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r) (hDpos : 0 < D)
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j)
    (j : Fin 9) : 0 < margProfile marg D j := by
  have h1 : (0 : ℝ) < (marg j : ℝ) := by
    exact_mod_cast marg_pos base marg hbase hmarg j
  have h2 : (0 : ℝ) < ((3 * D : ℕ) : ℝ) := by
    have : 0 < 3 * D := by omega
    exact_mod_cast this
  exact div_pos h1 h2

private theorem a_pos (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r) (hDpos : 0 < D)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ)) (i : Fin 10) : 0 < a i := by
  rw [ha]
  exact div_pos (baseReal_pos base hbase i) (by exact_mod_cast hDpos)

private theorem marginal_profile_eq
    (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hDpos : 0 < D)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ))
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j)
    (j : Fin 9) : marginal a j = margProfile marg D j := by
  have haf : a = fun i ↦ (base i : ℝ) / (D : ℝ) := funext ha
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  rw [marginal, haf, Q_smul, ← hmarg]
  unfold margProfile
  push_cast
  field_simp

private theorem profile_exponent_identity
    (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (D : ℕ) (hDpos : 0 < D)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ)) (m : ℕ) (i : Fin 10) :
    (a i / 3) * (((classMultiplicity i * (3 * D * m) : ℕ) : ℝ)) =
      ((classMultiplicity i * (base i * m) : ℕ) : ℝ) := by
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  rw [ha]
  push_cast
  field_simp

private theorem globalRate_pow_factorization
    (tau : ℝ) (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r) (hDpos : 0 < D)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ))
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j)
    (m : ℕ) :
    (globalRate 6 tau a a) ^ (3 * D * m) =
      capacityInner tau base m * marginalRate marg D ^ (3 * D * m) := by
  have hapos : ∀ i, 0 < a i := a_pos a base D hbase hDpos ha
  have hcancel (i : Fin 10) :
      Real.rpow (a i) (a i) * Real.rpow (a i) (-a i) = 1 := by
    change a i ^ a i * a i ^ (-a i) = 1
    rw [← Real.rpow_add (hapos i)]
    simp
  have houter :
      (∏ i : Fin 10,
        (Real.rpow (classValue 6 tau i) (a i / 3) *
          Real.rpow (a i) (a i) *
          Real.rpow (a i) (-a i)) ^ classMultiplicity i) =
        ∏ i : Fin 10,
          (Real.rpow (classValue 6 tau i) (a i / 3)) ^ classMultiplicity i := by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [mul_assoc, hcancel, mul_one]
  rw [globalRate, houter, mul_pow]
  congr 1
  · rw [← Finset.prod_pow]
    unfold capacityInner
    apply Finset.prod_congr rfl
    intro i _hi
    rw [← pow_mul]
    calc
      (Real.rpow (classValue 6 tau i) (a i / 3)) ^
            (classMultiplicity i * (3 * D * m)) =
          Real.rpow (classValue 6 tau i)
            ((a i / 3) * ((classMultiplicity i * (3 * D * m) : ℕ) : ℝ)) :=
        (Real.rpow_mul_natCast (classValue_pos tau i).le (a i / 3)
          (classMultiplicity i * (3 * D * m))).symm
      _ = Real.rpow (classValue 6 tau i)
          ((classMultiplicity i * (base i * m) : ℕ) : ℝ) := by
        rw [profile_exponent_identity a base D hDpos ha m i]
      _ = (classValue 6 tau i) ^ (classMultiplicity i * (base i * m)) :=
        Real.rpow_natCast _ _
  · unfold marginalRate
    apply congrArg (fun x : ℝ ↦ x ^ (3 * D * m))
    apply Finset.prod_congr rfl
    intro j _hj
    rw [marginal_profile_eq a base marg D hDpos ha hmarg]

private theorem marginal_multinomial_entropy_bound
    (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r) (hDpos : 0 < D)
    (hD : D = ∑ r : Fin 10, classMultiplicity r * base r)
    (hmarg : ∀ j, (marg j : ℝ) = Q (fun i ↦ (base i : ℝ)) j)
    (m : ℕ) (hm : 0 < m) :
    marginalRate marg D ^ (3 * D * m) ≤
      (6 * (((3 * D * m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) := by
  have hsum : ∑ j : Fin 9, marg j = 3 * D := marg_sum base marg D hD hmarg
  have hsumPos : 0 < ∑ j : Fin 9, marg j := by rw [hsum]; omega
  have hlower := mme_dwz_multinomial_entropy_polynomial_lower marg m hm hsumPos
  have hprofile :
      (fun j ↦ (marg j : ℝ) / (((∑ k : Fin 9, marg k : ℕ) : ℝ))) =
        margProfile marg D := by
    funext j
    rw [hsum]
    rfl
  rw [hprofile, hsum] at hlower
  have hentropy :=
    exp_log_two_entropyBits_eq_prod_rpow (margProfile marg D)
      (margProfile_pos base marg D hbase hDpos hmarg)
  have hlhs :
      Real.exp ((m : ℝ) * (((3 * D : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits (margProfile marg D))) =
        marginalRate marg D ^ (3 * D * m) := by
    rw [show (m : ℝ) * (((3 * D : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits (margProfile marg D)) =
        (((3 * D * m : ℕ)) : ℝ) *
          (Real.log 2 * mme_modern_entropyBits (margProfile marg D)) by
      push_cast
      ring]
    rw [Real.exp_nat_mul, hentropy]
    rfl
  rw [hlhs] at hlower
  simpa only [Fintype.card_fin, mul_assoc] using hlower

private noncomputable def polyC : ℝ :=
  (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) + 1

private theorem polynomial_le_exp_sqrt (N : ℕ) :
    (6 * (((N + 1 : ℕ) : ℝ))) ^ 9 ≤
      Real.exp (polyC * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp only [x]
    exact Real.sq_sqrt (by positivity)
  have hx1 : 1 ≤ x := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    linarith
  have h18 := Real.pow_div_factorial_le_exp x hx0 18
  have hpoly :
      (6 * (((N + 1 : ℕ) : ℝ))) ^ 9 ≤
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := by
    have hx18 : x ^ 18 ≤ (Nat.factorial 18 : ℝ) * Real.exp x := by
      have hfac : 0 < (Nat.factorial 18 : ℝ) := by positivity
      simpa [mul_comm] using (div_le_iff₀ hfac).mp h18
    calc
      (6 * (((N + 1 : ℕ) : ℝ))) ^ 9 = (6 : ℝ) ^ 9 * x ^ 18 := by
        rw [← hx2, mul_pow, ← pow_mul]
      _ ≤ (6 : ℝ) ^ 9 * ((Nat.factorial 18 : ℝ) * Real.exp x) :=
        mul_le_mul_of_nonneg_left hx18 (by positivity)
      _ = (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := by ring
  have hconst :
      (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) ≤ Real.exp ((polyC - 1) * x) := by
    have hExpLower := Real.add_one_le_exp ((polyC - 1) * x)
    have hxlarge :
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) ≤ 1 + (polyC - 1) * x := by
      have hc : polyC - 1 = (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) := by
        unfold polyC
        ring
      rw [hc]
      nlinarith [mul_le_mul_of_nonneg_left hx1
        (by positivity : 0 ≤ (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ))]
    exact hxlarge.trans (by simpa [add_comm] using hExpLower)
  calc
    (6 * (((N + 1 : ℕ) : ℝ))) ^ 9 ≤
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := hpoly
    _ ≤ Real.exp ((polyC - 1) * x) * Real.exp x := by gcongr
    _ = Real.exp (polyC * x) := by
      rw [← Real.exp_add]
      congr 1
      ring

end MME.StothersFourth.GeneralProfileRate

open MME.StothersFourth.GeneralProfileRate in
/-- **Equation (5.3) rate bookkeeping at an arbitrary integral ten-class
profile.**  The nine-letter marginal multinomial carries the whole scalar
part of the Davie--Stothers global rate at the profile `a = base / D`, up to
a single uniform `exp(-C sqrt N)` loss. -/
theorem solution
    (tau : ℝ) (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r)
    (hD : D = ∑ r : Fin 10, MME.StothersFourth.classMultiplicity r * base r)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ))
    (hmarg : ∀ j, (marg j : ℝ) =
      MME.StothersFourth.Q (fun i ↦ (base i : ℝ)) j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        (MME.StothersFourth.globalRate 6 tau a a) ^ (3 * D * m) *
            Real.exp (-C * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) ≤
          (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) *
            (∏ r : Fin 10,
              (MME.StothersFourth.classValue 6 tau r) ^
                (MME.StothersFourth.classMultiplicity r * (base r * m))) := by
  have hDpos : 0 < D := by
    rw [hD]; exact scale_pos base hbase
  refine ⟨polyC, by unfold polyC; positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmulti :=
    marginal_multinomial_entropy_bound base marg D hbase hDpos hD hmarg m hm
  have hpoly := polynomial_le_exp_sqrt (3 * D * m)
  have hinner : 0 ≤ capacityInner tau base m := by
    unfold capacityInner
    exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (classValue_pos tau i).le _
  have hmargnn : 0 ≤ marginalRate marg D ^ (3 * D * m) :=
    pow_nonneg (Finset.prod_nonneg fun j _ ↦
      (Real.rpow_pos_of_pos
        (margProfile_pos base marg D hbase hDpos hmarg j) _).le) _
  have hmargScaled :
      marginalRate marg D ^ (3 * D * m) *
          Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) ≤
        (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) := by
    calc
      marginalRate marg D ^ (3 * D * m) *
            Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) ≤
          ((6 * (((3 * D * m + 1 : ℕ) : ℝ))) ^ 9 *
              (Nat.multinomial Finset.univ
                (fun j : Fin 9 ↦ marg j * m) : ℝ)) *
            Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) := by
        gcongr
      _ ≤ (Real.exp (polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) *
              (Nat.multinomial Finset.univ
                (fun j : Fin 9 ↦ marg j * m) : ℝ)) *
            Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) := by
        gcongr
      _ = (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) := by
        rw [show
            Real.exp (polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) *
                (Nat.multinomial Finset.univ
                  (fun j : Fin 9 ↦ marg j * m) : ℝ) *
                Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) =
              (Nat.multinomial Finset.univ
                  (fun j : Fin 9 ↦ marg j * m) : ℝ) *
                (Real.exp (polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) *
                  Real.exp
                    (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ)))) by
          ring]
        rw [← Real.exp_add]
        simp
  rw [globalRate_pow_factorization tau a base marg D hbase hDpos ha hmarg m]
  show
    capacityInner tau base m * marginalRate marg D ^ (3 * D * m) *
        Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) ≤
      (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) *
        capacityInner tau base m
  calc
    capacityInner tau base m * marginalRate marg D ^ (3 * D * m) *
          Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) =
        capacityInner tau base m *
          (marginalRate marg D ^ (3 * D * m) *
            Real.exp (-polyC * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ)))) := by
      ring
    _ ≤ capacityInner tau base m *
        (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) := by
      gcongr
    _ = (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) *
        capacityInner tau base m := by
      ring
