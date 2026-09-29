-- Prove2me | solution 1 for mme_complete_split_112_outer_star_entropy_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T23:49:56.289307+00:00
-- url     : https://prove2.me/submissions/0606b5c0-ad6a-4604-be9c-d7b6882059ef

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Mathlib.Tactic

open scoped BigOperators
open Filter

set_option autoImplicit false
set_option warningAsError true

private theorem multinomial_three_choose (a b c : ℕ) :
    Nat.multinomial Finset.univ ![a, b, c] =
      Nat.choose (a + b + c) a * Nat.choose (b + c) b := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [huniv, Nat.multinomial_insert (by decide), Nat.binomial_eq_choose (by decide)]
  simp [Nat.add_assoc]

private theorem zcount_eq_multinomial (l g m : ℕ) :
    Nat.choose (2 * ((l + g) * m)) (l * m) *
        Nat.choose (2 * ((l + g) * m) - l * m) (l * m) =
      Nat.multinomial Finset.univ (fun i : Fin 3 ↦ ![l, l, 2 * g] i * m) := by
  have hvec : (fun i : Fin 3 ↦ ![l, l, 2 * g] i * m) =
      ![l * m, l * m, 2 * g * m] := by
    funext i
    fin_cases i <;> rfl
  have htotal : 2 * ((l + g) * m) = l * m + (l * m + 2 * g * m) := by ring
  rw [hvec, multinomial_three_choose, htotal, Nat.add_sub_cancel_left]
  simp only [Nat.add_assoc]

private theorem profile_weight_normalization (l g : ℕ) (hD : 0 < l + g) :
    (fun i : Fin 3 ↦ (![l, l, 2 * g] i : ℝ) /
      ((∑ j : Fin 3, ![l, l, 2 * g] j : ℕ) : ℝ)) =
    ![(l : ℝ) / (2 * ((l + g : ℕ) : ℝ)),
      (l : ℝ) / (2 * ((l + g : ℕ) : ℝ)),
      1 - 2 * ((l : ℝ) / (2 * ((l + g : ℕ) : ℝ)))] := by
  have hsum : (∑ j : Fin 3, ![l, l, 2 * g] j : ℕ) = 2 * (l + g) := by
    simp [Fin.sum_univ_succ]
    ring
  have hd : (g : ℝ) + (l : ℝ) ≠ 0 := by exact_mod_cast (show g + l ≠ 0 by omega)
  have hd' : (l : ℝ) + (g : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [hsum]
  funext i
  fin_cases i <;> simp
  field_simp [hd, hd']
  ring

private theorem zcount_entropy_polynomial_lower
    (l g m : ℕ) (hD : 0 < l + g) (hm : 0 < m) :
    let N : ℕ := (l + g) * m
    let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
    Real.exp ((2 * N : ℕ) * Real.log 2 *
      mme_modern_entropyBits ![p, p, 1 - 2 * p]) ≤
      (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ 3 *
        ((Nat.choose (2 * N) (l * m) *
          Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) := by
  have hsum : (∑ j : Fin 3, ![l, l, 2 * g] j : ℕ) = 2 * (l + g) := by
    simp [Fin.sum_univ_succ]
    ring
  have htotal : 0 < ∑ j : Fin 3, ![l, l, 2 * g] j := by rw [hsum]; omega
  have h := mme_dwz_multinomial_entropy_polynomial_lower ![l, l, 2 * g]
    m hm htotal
  rw [profile_weight_normalization l g hD, ← zcount_eq_multinomial l g m] at h
  simp only [Fintype.card_fin, hsum] at h
  dsimp only
  convert h using 1 <;> push_cast <;> ring

private theorem zcount_log_lower
    (l g m : ℕ) (hD : 0 < l + g) (hm : 0 < m)
    (C a : ℝ) (ha : 0 < a) :
    let N : ℕ := (l + g) * m
    let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
    (((Nat.choose (2 * N) (l * m) *
      Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) *
        Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ a) →
    (2 * N : ℕ) * Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] -
        3 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) -
        C * Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ Real.log a := by
  dsimp only
  let N : ℕ := (l + g) * m
  let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
  let E : ℝ := (2 * N : ℕ) * Real.log 2 *
    mme_modern_entropyBits ![p, p, 1 - 2 * p]
  let P : ℝ := (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ 3
  let Z : ℝ := ((Nat.choose (2 * N) (l * m) *
    Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ)
  intro hraw
  change Z * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ a at hraw
  change E - 3 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) -
    C * Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ Real.log a
  have hp := zcount_entropy_polynomial_lower l g m hD hm
  change Real.exp E ≤ P * Z at hp
  have hP : 0 < P := by dsimp [P]; positivity
  have hexp : Real.exp (E - C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ P * a := by
    calc
      _ = Real.exp E * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (P * Z) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = P * (Z * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ))) := by ring
      _ ≤ P * a := mul_le_mul_of_nonneg_left hraw hP.le
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp, Real.log_mul hP.ne' ha.ne'] at hlog
  dsimp only [P] at hlog
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

private theorem log_polynomial_loss_bound (N : ℕ) :
    3 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) ≤
      3 * Real.log ((N : ℝ) + 1) + 3 * Real.log 12 := by
  have hle : (6 : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ≤ 12 * ((N : ℝ) + 1) := by
    push_cast
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
    6 * ((2 * N + 1 : ℕ) : ℝ)) hle
  rw [Real.log_mul (show (12 : ℝ) ≠ 0 by norm_num) (by positivity)] at hlog
  linarith

theorem solution
    (l g : ℕ) (hD : 0 < l + g) (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N : ℕ := (l + g) * m
      let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
      ∀ a : ℝ, 0 < a →
        (((Nat.choose (2 * N) (l * m) *
          Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) *
            Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ a) →
        (2 * N : ℕ) *
          (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log a := by
  have habs := mme_log_sqrt_loss_eventually_le_linear 3 C (3 * Real.log 12)
    (2 * delta) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 habs
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ (l + g) * m := by
    have : m ≤ (l + g) * m := by simpa using Nat.mul_le_mul_right m hD
    omega
  have hsmall := hN₀ ((l + g) * m) hNm
  have hpoly := log_polynomial_loss_bound ((l + g) * m)
  dsimp only
  intro a ha hraw
  have hlog := zcount_log_lower l g m hD hmpos C a ha hraw
  push_cast at hlog ⊢
  push_cast at hsmall hpoly
  nlinarith only [hlog, hsmall, hpoly]

