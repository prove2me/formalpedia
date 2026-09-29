-- Prove2me | solution 2 for mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:41:59.949577+00:00
-- url     : https://prove2.me/submissions/fb56c8d7-8193-43ef-81ff-8d6941a12dd9

import Mathlib
import Theorems.Thm_mme_CW_q6_regular_primary_hash_large_uniform_family
import Theorems.Thm_mme_CW_q6_eventual_middle_dominates_hash_modulus
import Theorems.Thm_mme_CW_q6_explicit_behrend_half_modulus_strong_witness
import Theorems.Thm_mme_CW_q6_hash_modulus_le_five_mul_Zcount
import Theorems.Thm_mme_CW_q6_floor_rate_absorption

open MME Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem q6_large_uniform_family_at_N
    {N L G : ℕ}
    (hN : 0 < N)
    (hregular : CWQ6ExactAddressRegularity N L G)
    (hG : 0 < G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      ((4 * (Nat.choose N G) ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (hlarge :
      400 * (4 * (Nat.choose N G) ^ 2 + 1) ≤
        Nat.choose (2 * G) G) :
    ∃ A H : ℕ,
      Nonempty (CWQ6PrimaryHashFamily N L G A H) ∧
      (S.card * (cwQ6ExactZWords N L G).card) /
            (16 * (4 * (Nat.choose N G) ^ 2 + 1)) ≤ A ∧
      H = Nat.choose (2 * G) G /
            (8 * (4 * (Nat.choose N G) ^ 2 + 1)) := by
  cases N with
  | zero => omega
  | succ n =>
      simpa only [Nat.succ_eq_add_one] using
        (mme_CW_q6_regular_primary_hash_large_uniform_family
          (n := n) hregular hG S hSrange hSfree hlarge)

theorem solution
    (L G : ℕ → ℕ)
    (hregular : ∀ N : ℕ, L N + G N = N →
      CWQ6ExactAddressRegularity N (L N) (G N)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ :=
          Nat.choose (2 * N) (L N) *
            Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (0 < L N ∧ L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  let C : ℝ := 12 + Real.log 32
  have hlog : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards
      [mme_CW_q6_explicit_behrend_half_modulus_strong_witness,
       mme_CW_q6_eventual_middle_dominates_hash_modulus L G,
       eventually_ge_atTop (1 : ℕ)]
      with N hbehrend hlargeN hN
  dsimp only
  intro hprofile
  rcases hprofile with ⟨hL, hsum, hratio⟩
  have hG : 0 < G N := by omega
  have hGlt : G N < N := by omega
  have hGle : G N ≤ N := hGlt.le
  let Zcount : ℕ :=
    Nat.choose (2 * N) (L N) * Nat.choose (2 * N - L N) (L N)
  let Xcount : ℕ := Nat.choose N (G N)
  let middle : ℕ := Nat.choose (2 * G N) (G N)
  let M : ℕ := 4 * Xcount ^ 2 + 1
  have hreg := hregular N hsum
  obtain ⟨S, hSrange, hSfree, hS80, hdensity⟩ :=
    hbehrend (G N) hG hGlt
  have hlarge : 400 * M ≤ middle := by
    simpa only [M, Xcount, middle] using
      hlargeN ⟨hsum, hratio⟩
  obtain ⟨A, H, hfamily, hAraw, hH⟩ :=
    q6_large_uniform_family_at_N (N := N) (L := L N) (G := G N)
      (by omega) hreg hG S
      (by simpa only [M, Xcount] using hSrange)
      hSfree
      (by simpa only [M, Xcount, middle] using hlarge)
  have hA : (S.card * Zcount) / (16 * M) ≤ A := by
    have hzcard := hreg.z_word_card
    simpa only [Zcount, M, Xcount, hzcard] using hAraw
  have hMZ : M ≤ 5 * Zcount := by
    simpa only [M, Xcount, Zcount] using
      (mme_CW_q6_hash_modulus_le_five_mul_Zcount
        (N := N) (L := L N) (G := G N) hsum)
  have hXpos : 0 < Xcount := by
    dsimp [Xcount]
    exact Nat.choose_pos hGle
  have hrates := mme_CW_q6_floor_rate_absorption
    (N := N) (S := S.card) (Z := Zcount) (X := Xcount)
    (B := middle) (M := M) (A := A) (H := H) (C := 12)
    (by norm_num) hXpos rfl hMZ hS80 hA hlarge
    (by simpa only [M, Xcount, middle] using hH)
    (by simpa only [M, Xcount] using hdensity)
  have hHpow : H ≤ 4 ^ N := by
    have hHB : H ≤ middle := by
      rw [hH]
      exact Nat.div_le_self _ _
    have hBpow : middle ≤ 2 ^ (2 * G N) := by
      dsimp [middle]
      exact Nat.choose_le_two_pow (2 * G N) (G N)
    have hpoweq : 2 ^ (2 * G N) = 4 ^ (G N) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    calc
      H ≤ middle := hHB
      _ ≤ 2 ^ (2 * G N) := hBpow
      _ = 4 ^ (G N) := hpoweq
      _ ≤ 4 ^ N := by
        gcongr
        norm_num
  obtain ⟨family⟩ := hfamily
  refine ⟨A, H, family, hHpow, ?_, ?_⟩
  · simpa only [C, Zcount] using hrates.1
  · simpa only [C, middle, Xcount] using hrates.2
