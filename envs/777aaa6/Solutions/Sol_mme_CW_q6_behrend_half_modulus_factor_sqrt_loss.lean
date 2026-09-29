-- Prove2me | solution 1 for mme_CW_q6_behrend_half_modulus_factor_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:28:08.59998+00:00
-- url     : https://prove2.me/submissions/4d925944-65df-4970-a19b-574dc6ad49a7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Sqrt
import Theorems.Thm_mme_behrend_explicit_threeAP_free

open Filter Topology

/-- A Behrend set in the lower half of the odd hashing modulus retains every
fixed density power and every fixed polynomial loss up to `exp (-C * sqrt N)`.
The lower-half placement is what turns modular three-term-progression
collisions into ordinary natural-number equalities. -/
theorem solution (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ G : ℕ, G ≤ N →
          let Xcount : ℕ := Nat.choose N G
          let Mmod : ℕ := 4 * Xcount ^ 2 + 1
          ∃ S : Finset ℕ,
            S ⊆ Finset.range (Mmod / 2) ∧
            ThreeAPFree (S : Set ℕ) ∧
            0 < S.card ∧
            Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d) := by
  refine ⟨12 * (d : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro G hGN
  dsimp only
  let Xcount : ℕ := Nat.choose N G
  let Mmod : ℕ := 4 * Xcount ^ 2 + 1
  let R : ℕ := Mmod / 2
  have hXpos : 0 < Xcount := by
    dsimp [Xcount]
    exact Nat.choose_pos hGN
  have hRform : R = 2 * Xcount ^ 2 := by
    dsimp [R, Mmod]
    omega
  have hRposNat : 0 < R := by
    rw [hRform]
    positivity
  obtain ⟨S, hSrange, hSfree, hScard⟩ :=
    mme_behrend_explicit_threeAP_free R
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRposNat
  have hScardPosReal : (0 : ℝ) < (S.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hRpos (Real.exp_pos _)) hScard
  have hScardPos : 0 < S.card := by exact_mod_cast hScardPosReal
  refine ⟨S, by simpa [R] using hSrange, hSfree, hScardPos, ?_⟩

  have hMform : Mmod = 2 * R + 1 := by
    rw [hRform]
    dsimp [Mmod]
    ring
  have hMposNat : 0 < Mmod := by
    rw [hMform]
    omega
  have hMpos : (0 : ℝ) < (Mmod : ℝ) := by exact_mod_cast hMposNat
  have hMleThreeRNat : Mmod ≤ 3 * R := by
    rw [hMform]
    omega
  have hMleThreeR : (Mmod : ℝ) ≤ 3 * (R : ℝ) := by
    exact_mod_cast hMleThreeRNat

  have hXbound : Xcount ≤ 2 ^ N := by
    dsimp [Xcount]
    exact Nat.choose_le_two_pow N G
  have hXsq : Xcount ^ 2 ≤ (2 ^ N) ^ 2 :=
    Nat.pow_le_pow_left hXbound 2
  have hMboundNat : Mmod ≤ 2 * 4 ^ (N + 1) := by
    dsimp [Mmod]
    have hpow : (2 ^ N) ^ 2 = 4 ^ N := by
      calc
        (2 ^ N) ^ 2 = 2 ^ (N * 2) := by rw [pow_mul]
        _ = 2 ^ (2 * N) := by congr 1 <;> omega
        _ = (2 ^ 2) ^ N := by rw [pow_mul]
        _ = 4 ^ N := by norm_num
    rw [hpow] at hXsq
    have hstep : 4 * Xcount ^ 2 ≤ 4 ^ (N + 1) := by
      calc
        4 * Xcount ^ 2 ≤ 4 * 4 ^ N := Nat.mul_le_mul_left 4 hXsq
        _ = 4 ^ (N + 1) := by rw [pow_succ]; ring
    omega
  have hMbound : (Mmod : ℝ) ≤ 2 * (4 : ℝ) ^ (N + 1) := by
    exact_mod_cast hMboundNat
  have hRleMNat : R ≤ Mmod := by
    rw [hMform]
    omega
  have hRleM : (R : ℝ) ≤ (Mmod : ℝ) := by exact_mod_cast hRleMNat

  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNoneNat : 1 ≤ N := hN
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNoneNat
  have hNp1 : 0 < (N : ℝ) + 1 := by positivity
  have hNp1nonneg : 0 ≤ (N : ℝ) + 1 := hNp1.le
  have hsqrtOne : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt ((N : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by nlinarith)

  have hlogM : Real.log (Mmod : ℝ) ≤ 4 * ((N : ℝ) + 1) := by
    have hlogMono := Real.log_le_log hMpos hMbound
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogFour : Real.log (4 : ℝ) ≤ 3 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero (N + 1) (by norm_num : (4 : ℝ) ≠ 0)),
      Real.log_pow] at hlogMono
    push_cast at hlogMono
    have hscaled := mul_le_mul_of_nonneg_left hlogFour
      (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
    nlinarith
  have hlogR : Real.log (R : ℝ) ≤ 4 * ((N : ℝ) + 1) := by
    exact (Real.log_le_log hRpos hRleM).trans hlogM
  have hsqrtLog :
      Real.sqrt (Real.log (R : ℝ)) ≤
        2 * Real.sqrt ((N : ℝ) + 1) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hNp1nonneg]

  have hscaledCardR :
      Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) ≤
        (S.card : ℝ) / (R : ℝ) := by
    exact (le_div_iff₀ hRpos).2 (by simpa [mul_comm] using hScard)
  have hthirdScaledCardR :
      (1 / 3 : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) ≤
        (S.card : ℝ) / (Mmod : ℝ) := by
    apply (le_div_iff₀ hMpos).2
    have hthirdM : (1 / 3 : ℝ) * (Mmod : ℝ) ≤ (R : ℝ) := by
      nlinarith
    calc
      (1 / 3 : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) *
            (Mmod : ℝ)
          = ((1 / 3 : ℝ) * (Mmod : ℝ)) *
              Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) := by ring
      _ ≤ (R : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) := by
            gcongr
      _ ≤ (S.card : ℝ) := hScard

  have hlogThree : Real.log (3 : ℝ) ≤ 2 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hthird :
      Real.exp (-2 * Real.sqrt ((N : ℝ) + 1)) ≤ (1 / 3 : ℝ) := by
    have hthirdEq : (1 / 3 : ℝ) = Real.exp (-Real.log 3) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_num
    rw [hthirdEq]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbehrendExp :
      Real.exp (-8 * Real.sqrt ((N : ℝ) + 1)) ≤
        Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbase :
      Real.exp (-10 * Real.sqrt ((N : ℝ) + 1)) ≤
        (S.card : ℝ) / (Mmod : ℝ) := by
    calc
      Real.exp (-10 * Real.sqrt ((N : ℝ) + 1)) =
          Real.exp (-2 * Real.sqrt ((N : ℝ) + 1)) *
            Real.exp (-8 * Real.sqrt ((N : ℝ) + 1)) := by
              rw [← Real.exp_add]
              congr 1
              ring
      _ ≤ (1 / 3 : ℝ) *
            Real.exp (-4 * Real.sqrt (Real.log (R : ℝ))) := by
              gcongr
      _ ≤ (S.card : ℝ) / (Mmod : ℝ) := hthirdScaledCardR
  have hbasePow :
      Real.exp (-10 * (d : ℝ) * Real.sqrt ((N : ℝ) + 1)) ≤
        ((S.card : ℝ) / (Mmod : ℝ)) ^ d := by
    calc
      Real.exp (-10 * (d : ℝ) * Real.sqrt ((N : ℝ) + 1)) =
          (Real.exp (-10 * Real.sqrt ((N : ℝ) + 1))) ^ d := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ ≤ ((S.card : ℝ) / (Mmod : ℝ)) ^ d := by
            exact pow_le_pow_left₀ (Real.exp_nonneg _) hbase d

  have hlogNp1 :
      Real.log ((N : ℝ) + 1) ≤ 2 * Real.sqrt ((N : ℝ) + 1) := by
    have hsqrtPos : 0 < Real.sqrt ((N : ℝ) + 1) := by positivity
    have hbasic := Real.log_le_sub_one_of_pos hsqrtPos
    rw [Real.log_sqrt hNp1nonneg] at hbasic
    nlinarith
  have hpoly :
      ((N : ℝ) + 1) ^ d ≤
        Real.exp (2 * (d : ℝ) * Real.sqrt ((N : ℝ) + 1)) := by
    apply (Real.log_le_iff_le_exp (pow_pos hNp1 d)).mp
    rw [Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlogNp1 (Nat.cast_nonneg d)]
  rw [Nat.cast_add, Nat.cast_one]
  apply (le_div_iff₀ (pow_pos hNp1 d)).2
  calc
    Real.exp (-(12 * (d : ℝ)) * Real.sqrt ((N : ℝ) + 1)) *
          ((N : ℝ) + 1) ^ d
        ≤ Real.exp (-(12 * (d : ℝ)) * Real.sqrt ((N : ℝ) + 1)) *
            Real.exp (2 * (d : ℝ) * Real.sqrt ((N : ℝ) + 1)) := by
              gcongr
    _ = Real.exp (-10 * (d : ℝ) * Real.sqrt ((N : ℝ) + 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ ((S.card : ℝ) / (Mmod : ℝ)) ^ d := hbasePow
