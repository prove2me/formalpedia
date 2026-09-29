-- Prove2me | solution 1 for mme_CW_q6_explicit_behrend_half_modulus_strong_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:33:09.665465+00:00
-- url     : https://prove2.me/submissions/6eaef6b0-599b-43fd-9440-6ff62367f1b7

import Mathlib
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty

open Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma q6_log_half_modulus_le
    {N G : ℕ} (hGN : G ≤ N) :
    let X : ℕ := Nat.choose N G
    let Q : ℕ := (4 * X ^ 2 + 1) / 2
    Real.log (Q : ℝ) ≤ 2 * ((N + 1 : ℕ) : ℝ) := by
  dsimp only
  let X : ℕ := Nat.choose N G
  let Q : ℕ := (4 * X ^ 2 + 1) / 2
  have hX : X ≤ 2 ^ N := by
    dsimp [X]
    exact Nat.choose_le_two_pow N G
  have hXpos : 0 < X := by
    dsimp [X]
    exact Nat.choose_pos hGN
  have hQformula : Q = 2 * X ^ 2 := by
    dsimp [Q]
    omega
  have hQpow : Q ≤ 2 ^ (2 * N + 1) := by
    rw [hQformula]
    calc
      2 * X ^ 2 ≤ 2 * (2 ^ N) ^ 2 := by gcongr
      _ = 2 ^ (2 * N + 1) := by
        rw [← pow_mul]
        ring_nf
  have hQposNat : 0 < Q := by rw [hQformula]; positivity
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQposNat
  have hpowpos : 0 < ((2 : ℝ) ^ (2 * N + 1)) := by positivity
  have hlogmono :
      Real.log (Q : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 * N + 1)) := by
    exact Real.strictMonoOn_log.monotoneOn
      hQpos hpowpos (by exact_mod_cast hQpow)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log (2 : ℝ) ≤ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      _ = 1 := by norm_num
  calc
    Real.log (Q : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 * N + 1)) := hlogmono
    _ = ((2 * N + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (2 * N + 1)
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) * 1 := by gcongr
    _ ≤ 2 * ((N + 1 : ℕ) : ℝ) := by push_cast; nlinarith

private lemma q6_three_mul_succ_le_exp_four_sqrt (N : ℕ) :
    3 * (((N + 1 : ℕ) : ℝ) ) ≤
      Real.exp (4 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N)))
  have hrsq : r ^ 2 = ((N + 1 : ℕ) : ℝ) := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hexp : 1 + 2 * r ≤ Real.exp (2 * r) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 * r)
  have hsq : 3 * r ^ 2 ≤ (1 + 2 * r) ^ 2 := by nlinarith
  have hsqexp : (1 + 2 * r) ^ 2 ≤ (Real.exp (2 * r)) ^ 2 := by
    gcongr
  calc
    3 * (((N + 1 : ℕ) : ℝ)) = 3 * r ^ 2 := by rw [hrsq]
    _ ≤ (1 + 2 * r) ^ 2 := hsq
    _ ≤ (Real.exp (2 * r)) ^ 2 := hsqexp
    _ = Real.exp (4 * r) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

private lemma q6_exp_twelve_sqrt_density_le
    {N G S : ℕ}
    (hGN : G ≤ N)
    (hS :
      (((4 * (Nat.choose N G) ^ 2 + 1) / 2 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log ((((4 * (Nat.choose N G) ^ 2 + 1) / 2 : ℕ) : ℝ)))) ≤
        (S : ℝ)) :
    Real.exp (-12 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      (S : ℝ) / (4 * (Nat.choose N G) ^ 2 + 1 : ℕ) /
        (((N + 1 : ℕ) : ℝ)) := by
  let X : ℕ := Nat.choose N G
  let M : ℕ := 4 * X ^ 2 + 1
  let Q : ℕ := M / 2
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hXpos : 0 < X := by
    dsimp [X]
    exact Nat.choose_pos hGN
  have hQformula : Q = 2 * X ^ 2 := by dsimp [Q, M]; omega
  have hQpos : 0 < Q := by rw [hQformula]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMQ : M ≤ 3 * Q := by
    rw [hQformula]
    dsimp [M]
    have : 1 ≤ X ^ 2 := by nlinarith
    omega
  have hlog : Real.log (Q : ℝ) ≤ 2 * (((N + 1 : ℕ) : ℝ)) := by
    simpa only [X, M, Q] using q6_log_half_modulus_le hGN
  have hlognonneg : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hQpos)
  have hsqrtlog : Real.sqrt (Real.log (Q : ℝ)) ≤ 2 * r := by
    have hsqrt := Real.sqrt_le_sqrt hlog
    have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = ((N + 1 : ℕ) : ℝ) := by
      dsimp [r]
      exact Real.sq_sqrt (by positivity)
    have hsq2 : Real.sqrt (2 * (((N + 1 : ℕ) : ℝ))) ≤ 2 * r := by
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
      rw [Real.sq_sqrt (by positivity)]
      nlinarith
    exact hsqrt.trans hsq2
  have hexpcomp : Real.exp (-8 * r) ≤
      Real.exp (-4 * Real.sqrt (Real.log (Q : ℝ))) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hS' :
      (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (Q : ℝ))) ≤
        (S : ℝ) := by
    simpa only [X, M, Q] using hS
  have hthree := q6_three_mul_succ_le_exp_four_sqrt N
  have hdenpos : 0 < (M : ℝ) := by exact_mod_cast hMpos
  have hNpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hMQr : (M : ℝ) ≤ 3 * (Q : ℝ) := by exact_mod_cast hMQ
  have hQnonneg : 0 ≤ (Q : ℝ) := by positivity
  have hexpid : Real.exp (-12 * r) =
      Real.exp (-8 * r) / Real.exp (4 * r) := by
    calc
      Real.exp (-12 * r) = Real.exp (-8 * r + (-4 * r)) := by
        congr 1
        ring
      _ = Real.exp (-8 * r) * Real.exp (-4 * r) := Real.exp_add _ _
      _ = Real.exp (-8 * r) / Real.exp (4 * r) := by
        rw [show -4 * r = -(4 * r) by ring, Real.exp_neg]
        ring
  have hcore :
      Real.exp (-12 * r) * (M : ℝ) * (((N + 1 : ℕ) : ℝ)) ≤
        (S : ℝ) := by
    calc
      Real.exp (-12 * r) * (M : ℝ) * (((N + 1 : ℕ) : ℝ))
          ≤ Real.exp (-12 * r) * (3 * (Q : ℝ)) *
              (((N + 1 : ℕ) : ℝ)) := by gcongr
      _ = (Q : ℝ) * Real.exp (-8 * r) *
            (3 * (((N + 1 : ℕ) : ℝ)) / Real.exp (4 * r)) := by
          rw [hexpid]
          ring
      _ ≤ (Q : ℝ) * Real.exp (-8 * r) * 1 := by
          gcongr
          rw [div_le_one (Real.exp_pos _)]
          exact hthree
      _ ≤ (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (Q : ℝ))) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hexpcomp hQnonneg
      _ ≤ (S : ℝ) := hS'
  rw [div_div]
  apply (le_div_iff₀ (mul_pos hdenpos hNpos)).2
  simpa only [mul_assoc] using hcore

theorem solution :
    ∀ᶠ N : ℕ in atTop,
      ∀ G : ℕ, 0 < G → G < N →
        let X : ℕ := Nat.choose N G
        let M : ℕ := 4 * X ^ 2 + 1
        ∃ S : Finset ℕ,
          S ⊆ Finset.range (M / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧
          80 ≤ S.card ∧
          Real.exp (-12 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (S.card : ℝ) / (M : ℝ) /
              (((N + 1 : ℕ) : ℝ)) := by
  filter_upwards
      [mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty]
      with N hlarge
  intro G hG hGN
  dsimp only
  let X : ℕ := Nat.choose N G
  let M : ℕ := 4 * X ^ 2 + 1
  let Q : ℕ := M / 2
  obtain ⟨S, hSrange, hSfree, hSbound⟩ :=
    mme_behrend_explicit_threeAP_free Q
  have h80real : (80 : ℝ) ≤ (S.card : ℝ) :=
    (hlarge G hG hGN).trans (by simpa only [X, M, Q] using hSbound)
  have h80 : 80 ≤ S.card := by exact_mod_cast h80real
  refine ⟨S, ?_, hSfree, h80, ?_⟩
  · simpa only [M, Q] using hSrange
  · exact q6_exp_twelve_sqrt_density_le hGN.le (by
      simpa only [X, M, Q] using hSbound)
