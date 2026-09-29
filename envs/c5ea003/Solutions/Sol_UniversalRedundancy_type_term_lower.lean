-- Prove2me | solution 1 for UniversalRedundancy.type_term_lower
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T17:30:19.946866+00:00
-- url     : https://prove2.me/submissions/9add7144-f8b9-45e8-8b70-f4face9f37c5

import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Types

open Finset Real

open UniversalRedundancy

/-- Explicit Stirling upper bound: `m! ≤ e·√m·(m/e)^m` for `m ≥ 1`. -/
private theorem factorial_le_stirling_upper (m : ℕ) (hm : 1 ≤ m) :
    (Nat.factorial m : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le t)
  simp only [Function.comp] at h
  rw [Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hpos : (0:ℝ) < Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) * (((t+1:ℕ):ℝ) / Real.exp 1) ^ (t+1) := by
    have h1 : (0:ℝ) < ((t+1:ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [div_le_iff₀ hpos] at h
  refine le_trans h (le_of_eq ?_)
  have hs : Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt ((t+1:ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hs]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- Numerical endgame of `type_term_lower`, isolated for elaboration speed. -/
private lemma type_term_endgame (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) (b : ℝ) (hb : 0 < b)
    (step3 : Real.sqrt (2 * π * ((k + j : ℕ) : ℝ))
      ≤ b * (Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j))) :
    1 / (2 * Real.sqrt ((k + j : ℕ) : ℝ)) ≤ b := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hnR : (0:ℝ) < ((k+j : ℕ) : ℝ) := by push_cast; linarith
  have hsn : (0:ℝ) < Real.sqrt ((k+j:ℕ):ℝ) := Real.sqrt_pos.mpr hnR
  have hsplit : Real.sqrt (2 * π * ((k+j : ℕ) : ℝ))
      = Real.sqrt (2 * π) * Real.sqrt ((k+j:ℕ):ℝ) := Real.sqrt_mul (by positivity) _
  have hnn : Real.sqrt ((k+j:ℕ):ℝ) * Real.sqrt ((k+j:ℕ):ℝ) = ((k+j:ℕ):ℝ) :=
    Real.mul_self_sqrt hnR.le
  have hgeom : Real.sqrt k * Real.sqrt j ≤ ((k+j:ℕ):ℝ) / 2 := by
    have h1 : Real.sqrt k * Real.sqrt j = Real.sqrt ((k:ℝ) * (j:ℝ)) :=
      (Real.sqrt_mul hkR.le _).symm
    have h2 : (k:ℝ) * (j:ℝ) ≤ (((k+j:ℕ):ℝ)/2)^2 := by
      push_cast; nlinarith [sq_nonneg ((k:ℝ) - j)]
    rw [h1]
    calc Real.sqrt ((k:ℝ) * j) ≤ Real.sqrt ((((k+j:ℕ):ℝ)/2)^2) := Real.sqrt_le_sqrt h2
      _ = ((k+j:ℕ):ℝ)/2 := Real.sqrt_sq (by positivity)
  have h2pi : (2.5:ℝ) ≤ Real.sqrt (2 * π) := by
    have hle : (2.5:ℝ)^2 ≤ 2 * π := by nlinarith [Real.pi_gt_d2]
    calc (2.5:ℝ) = Real.sqrt ((2.5:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (2 * π) := Real.sqrt_le_sqrt hle
  have he2 : Real.exp 1 ^ 2 ≤ 7.4 := by nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  rw [hsplit] at step3
  have hstep : (2.5:ℝ) * Real.sqrt ((k+j:ℕ):ℝ) ≤ b * (7.4 * (((k+j:ℕ):ℝ)/2)) := by
    have h1 : b * (Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j))
        ≤ b * (7.4 * (((k+j:ℕ):ℝ)/2)) := by
      have hprod : Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j) ≤ 7.4 * (((k+j:ℕ):ℝ)/2) := by
        have h3 : (0:ℝ) ≤ Real.sqrt k * Real.sqrt j := by positivity
        nlinarith [Real.exp_pos 1]
      exact mul_le_mul_of_nonneg_left hprod hb.le
    nlinarith [h2pi, hsn]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt ((k+j:ℕ):ℝ))]
  nlinarith [hstep, hnn, hsn, hb]

theorem solution (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    1 / (2 * Real.sqrt ((k + j : ℕ) : ℝ))
      ≤ (((k + j).choose k : ℕ) : ℝ) * ((k:ℝ)/((k+j:ℕ):ℝ))^k * ((j:ℝ)/((k+j:ℕ):ℝ))^j := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hnR : (0:ℝ) < ((k+j : ℕ) : ℝ) := by push_cast; linarith
  have hkn : k ≤ k + j := by omega
  have hsub : k + j - k = j := by omega
  have hfact : (Nat.factorial (k+j) : ℝ)
      = (((k+j).choose k : ℕ) : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial j : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hkn
    rw [hsub] at h
    exact_mod_cast h.symm
  have hlow := Stirling.le_factorial_stirling (k+j)
  have huk := factorial_le_stirling_upper k hk
  have huj := factorial_le_stirling_upper j hj
  set C : ℝ := (((k + j).choose k : ℕ) : ℝ) with hC
  have hCpos : 0 < C := by rw [hC]; exact_mod_cast Nat.choose_pos hkn
  set P : ℝ := ((k:ℝ)/((k+j:ℕ):ℝ))^k * ((j:ℝ)/((k+j:ℕ):ℝ))^j with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  set Q : ℝ := ((k:ℝ)/Real.exp 1)^k * ((j:ℝ)/Real.exp 1)^j with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hident : (((k+j : ℕ) : ℝ) / Real.exp 1) ^ (k+j) * P = Q := by
    rw [hP, hQ, div_pow, div_pow, div_pow, div_pow, div_pow, pow_add, pow_add]
    field_simp
  have step1 : Real.sqrt (2 * π * ((k+j : ℕ) : ℝ)) * (((k+j:ℕ):ℝ) / Real.exp 1) ^ (k+j)
      ≤ C * (Real.exp 1 * Real.sqrt k * ((k:ℝ)/Real.exp 1)^k)
          * (Real.exp 1 * Real.sqrt j * ((j:ℝ)/Real.exp 1)^j) := by
    refine le_trans hlow ?_
    rw [hfact]
    have h1 : (Nat.factorial k : ℝ) * (Nat.factorial j : ℝ)
        ≤ (Real.exp 1 * Real.sqrt k * ((k:ℝ)/Real.exp 1)^k)
          * (Real.exp 1 * Real.sqrt j * ((j:ℝ)/Real.exp 1)^j) := by
      have hk0 : (0:ℝ) ≤ (Nat.factorial k : ℝ) := by positivity
      have hj0 : (0:ℝ) ≤ (Nat.factorial j : ℝ) := by positivity
      have hu0 : (0:ℝ) ≤ Real.exp 1 * Real.sqrt k * ((k:ℝ)/Real.exp 1)^k := by positivity
      nlinarith [huk, huj]
    nlinarith [hCpos, h1]
  have step2 : Real.sqrt (2 * π * ((k+j : ℕ) : ℝ)) * Q
      ≤ (C * P) * (Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j)) * Q := by
    have hmul := mul_le_mul_of_nonneg_right step1 hPpos.le
    calc Real.sqrt (2 * π * ((k+j : ℕ) : ℝ)) * Q
        = Real.sqrt (2 * π * ((k+j : ℕ) : ℝ)) * ((((k+j:ℕ):ℝ) / Real.exp 1) ^ (k+j) * P) := by
          rw [← hident]
      _ = (Real.sqrt (2 * π * ((k+j : ℕ) : ℝ)) * (((k+j:ℕ):ℝ) / Real.exp 1) ^ (k+j)) * P := by
          ring
      _ ≤ (C * (Real.exp 1 * Real.sqrt k * ((k:ℝ)/Real.exp 1)^k)
            * (Real.exp 1 * Real.sqrt j * ((j:ℝ)/Real.exp 1)^j)) * P := hmul
      _ = (C * P) * (Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j)) * Q := by
          rw [hQ]; ring_nf; try ring
  have step3 : Real.sqrt (2 * π * ((k+j : ℕ) : ℝ))
      ≤ (C * P) * (Real.exp 1 ^ 2 * (Real.sqrt k * Real.sqrt j)) :=
    (le_of_mul_le_mul_right (by
      -- step2 : sqrt * Q ≤ (C*P)*(e^2*(√k*√j)) * Q
      convert step2 using 1 <;> ring) hQpos)
  have hCP : 0 < C * P := mul_pos hCpos hPpos
  have hgoal : 1 / (2 * Real.sqrt ((k + j : ℕ) : ℝ)) ≤ C * P :=
    type_term_endgame k j hk hj (C * P) hCP step3
  calc 1 / (2 * Real.sqrt ((k + j : ℕ) : ℝ)) ≤ C * P := hgoal
    _ = C * ((k:ℝ)/((k+j:ℕ):ℝ))^k * ((j:ℝ)/((k+j:ℕ):ℝ))^j := by rw [hP]; ring
