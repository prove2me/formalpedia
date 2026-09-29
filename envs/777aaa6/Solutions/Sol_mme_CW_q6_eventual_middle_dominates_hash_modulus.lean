-- Prove2me | solution 1 for mme_CW_q6_eventual_middle_dominates_hash_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:32:05.271488+00:00
-- url     : https://prove2.me/submissions/94989d8b-16ee-4590-b74f-d185a2aa83c7

import Mathlib

open BigOperators Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem q6_eventually_polynomial_times_ten_pow_le_eleven_pow :
    ∀ᶠ g : ℕ in atTop,
      (2000 * (2 * g + 1)) ^ 75 * 10 ^ g ≤ 11 ^ g := by
  have hbase :
      Tendsto
        (fun g : ℕ =>
          (g : ℝ) ^ 75 * ((10 : ℝ) / 11) ^ g)
        atTop (𝓝 0) := by
    exact tendsto_pow_const_mul_const_pow_of_lt_one 75 (by norm_num) (by norm_num)
  have hlim :
      Tendsto
        (fun g : ℕ =>
          (6000 : ℝ) ^ 75 *
            ((g : ℝ) ^ 75 * ((10 : ℝ) / 11) ^ g))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul ((6000 : ℝ) ^ 75)
  have hevent :
      ∀ᶠ g : ℕ in atTop,
        (6000 : ℝ) ^ 75 *
            ((g : ℝ) ^ 75 * ((10 : ℝ) / 11) ^ g) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hevent, eventually_ge_atTop 1] with g hg hg1
  have hlinear : 2000 * (2 * g + 1) ≤ 6000 * g := by omega
  have hratio :
      (6000 : ℝ) ^ 75 * (g : ℝ) ^ 75 *
          (((10 : ℝ) ^ g) / ((11 : ℝ) ^ g)) < 1 := by
    simpa only [div_pow, mul_assoc] using hg
  have hden : 0 < ((11 : ℝ) ^ g) := by positivity
  have hexp :
      (6000 : ℝ) ^ 75 * (g : ℝ) ^ 75 * (10 : ℝ) ^ g <
        (11 : ℝ) ^ g := by
    apply (div_lt_one hden).mp
    simpa only [mul_div_assoc] using hratio
  have hlinR : (2000 * (2 * g + 1) : ℝ) ≤ 6000 * g := by
    exact_mod_cast hlinear
  have hmainR :
      ((2000 * (2 * g + 1) : ℕ) : ℝ) ^ 75 * (10 : ℝ) ^ g ≤
        (11 : ℝ) ^ g := by
    calc
      ((2000 * (2 * g + 1) : ℕ) : ℝ) ^ 75 * (10 : ℝ) ^ g
          ≤ ((6000 * g : ℕ) : ℝ) ^ 75 * (10 : ℝ) ^ g := by
            gcongr
      _ = (6000 : ℝ) ^ 75 * (g : ℝ) ^ 75 * (10 : ℝ) ^ g := by
            push_cast
            rw [mul_pow]
      _ ≤ (11 : ℝ) ^ g := hexp.le
  exact_mod_cast hmainR

private theorem q6_choose_weighted_upper (L G : ℕ) :
    Nat.choose (L + G) G * 22 ^ L * 75 ^ G ≤ 97 ^ (L + G) := by
  have hmem : L ∈ Finset.range (L + G + 1) := by simp
  have hterm :
      22 ^ L * 75 ^ ((L + G) - L) * Nat.choose (L + G) L ≤
        ∑ k ∈ Finset.range (L + G + 1),
          22 ^ k * 75 ^ ((L + G) - k) * Nat.choose (L + G) k := by
    exact Finset.single_le_sum
      (f := fun k =>
        (22 : ℕ) ^ k * 75 ^ ((L + G) - k) * Nat.choose (L + G) k)
      (fun _ _ => Nat.zero_le _) hmem
  have hsum :
      (∑ k ∈ Finset.range (L + G + 1),
          (22 : ℕ) ^ k * 75 ^ ((L + G) - k) * Nat.choose (L + G) k) =
        97 ^ (L + G) := by
    simpa only [show (22 : ℕ) + 75 = 97 by norm_num] using
      (add_pow (22 : ℕ) 75 (L + G)).symm
  rw [hsum] at hterm
  calc
    Nat.choose (L + G) G * 22 ^ L * 75 ^ G =
        Nat.choose (L + G) L * 22 ^ L * 75 ^ G := by
          rw [Nat.choose_symm_add]
    _ ≤ 97 ^ (L + G) := by
      simpa [Nat.add_sub_cancel_left, mul_assoc, mul_left_comm, mul_comm] using hterm

private theorem q6_pow_swap
    {a b x y : ℕ} (hab : a ≤ b) (hxy : x ≤ y) :
    y ^ a * x ^ b ≤ x ^ a * y ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  simp only [pow_add]
  have hpow : x ^ d ≤ y ^ d := Nat.pow_le_pow_left hxy d
  calc
    y ^ a * (x ^ a * x ^ d) = (x * y) ^ a * x ^ d := by
      rw [mul_pow]
      ring
    _ ≤ (x * y) ^ a * y ^ d := by gcongr
    _ = x ^ a * (y ^ a * y ^ d) := by
      rw [mul_pow]
      ring

private theorem q6_block_ratio :
    11 * 97 ^ 194 ≤ 10 * (4 ^ 75 * 75 ^ 150 * 22 ^ 44) := by
  norm_num

private theorem q6_eventually_weighted_binomial_gap :
    ∀ᶠ G : ℕ in atTop,
      ∀ L : ℕ, 341 * L < 100 * G →
        2000 * (2 * G + 1) * 97 ^ (2 * (L + G)) ≤
          4 ^ G * 22 ^ (2 * L) * 75 ^ (2 * G) := by
  filter_upwards [q6_eventually_polynomial_times_ten_pow_le_eleven_pow]
      with G hpoly
  intro L hratio
  let D : ℕ := 2000 * (2 * G + 1)
  let P : ℕ := 4 ^ 75 * 75 ^ 150 * 22 ^ 44
  let Q : ℕ := 97 ^ 194
  have hratio' : 150 * L ≤ 44 * G := by omega
  have hblock : 11 * Q ≤ 10 * P := by
    simpa only [P, Q] using q6_block_ratio
  have hblockpow : 11 ^ G * Q ^ G ≤ 10 ^ G * P ^ G := by
    have := Nat.pow_le_pow_left hblock G
    simpa only [mul_pow] using this
  have hpoly' : D ^ 75 * 10 ^ G ≤ 11 ^ G := by
    simpa only [D] using hpoly
  have hcancelled : D ^ 75 * Q ^ G ≤ P ^ G := by
    have hwith :
        10 ^ G * (D ^ 75 * Q ^ G) ≤ 10 ^ G * P ^ G := by
      calc
        10 ^ G * (D ^ 75 * Q ^ G) =
            (D ^ 75 * 10 ^ G) * Q ^ G := by ring
        _ ≤ 11 ^ G * Q ^ G := by gcongr
        _ ≤ 10 ^ G * P ^ G := hblockpow
    exact Nat.le_of_mul_le_mul_left hwith (by positivity)
  have hswap :
      97 ^ (150 * L) * 22 ^ (44 * G) ≤
        22 ^ (150 * L) * 97 ^ (44 * G) :=
    q6_pow_swap hratio' (by norm_num)
  have hraised :
      (D * 97 ^ (2 * (L + G))) ^ 75 ≤
        (4 ^ G * 22 ^ (2 * L) * 75 ^ (2 * G)) ^ 75 := by
    have hmul :
        (D ^ 75 * 97 ^ (150 * (L + G))) * 22 ^ (44 * G) ≤
          (4 ^ (75 * G) * 22 ^ (150 * L) * 75 ^ (150 * G)) *
            22 ^ (44 * G) := by
      calc
        (D ^ 75 * 97 ^ (150 * (L + G))) * 22 ^ (44 * G) =
            D ^ 75 * 97 ^ (150 * G) *
              (97 ^ (150 * L) * 22 ^ (44 * G)) := by
                rw [Nat.mul_add, pow_add]
                ring
        _ ≤ D ^ 75 * 97 ^ (150 * G) *
              (22 ^ (150 * L) * 97 ^ (44 * G)) := by gcongr
        _ = 22 ^ (150 * L) *
              (D ^ 75 * (97 ^ 194) ^ G) := by
                rw [← pow_mul]
                ring
        _ ≤ 22 ^ (150 * L) * P ^ G := by
              exact Nat.mul_le_mul_left _ (by simpa only [Q] using hcancelled)
        _ = (4 ^ (75 * G) * 22 ^ (150 * L) * 75 ^ (150 * G)) *
              22 ^ (44 * G) := by
                have hPpow :
                    P ^ G =
                      4 ^ (75 * G) * 75 ^ (150 * G) * 22 ^ (44 * G) := by
                  change (4 ^ 75 * 75 ^ 150 * 22 ^ 44) ^ G = _
                  simp only [mul_pow, pow_mul]
                rw [hPpow]
                ring
    have hbase :
        D ^ 75 * 97 ^ (150 * (L + G)) ≤
          4 ^ (75 * G) * 22 ^ (150 * L) * 75 ^ (150 * G) :=
      Nat.le_of_mul_le_mul_right hmul (by positivity)
    calc
      (D * 97 ^ (2 * (L + G))) ^ 75 =
          D ^ 75 * 97 ^ (150 * (L + G)) := by
            rw [mul_pow, ← pow_mul]
            rw [show 2 * (L + G) * 75 = 150 * (L + G) by omega]
      _ ≤ 4 ^ (75 * G) * 22 ^ (150 * L) * 75 ^ (150 * G) := hbase
      _ = (4 ^ G * 22 ^ (2 * L) * 75 ^ (2 * G)) ^ 75 := by
            symm
            simp only [mul_pow]
            rw [← pow_mul, ← pow_mul, ← pow_mul]
            rw [show G * 75 = 75 * G by omega,
              show 2 * L * 75 = 150 * L by omega,
              show 2 * G * 75 = 150 * G by omega]
  have hbase :=
    (Nat.pow_le_pow_iff_left (show (75 : ℕ) ≠ 0 by norm_num)).mp hraised
  simpa only [D, Nat.mul_assoc] using hbase

private theorem q6_hash_modulus_le_central_of_weighted_gap
    {N L G : ℕ} (hLG : L + G = N) (hratio : 341 * L < 100 * G)
    (hgap :
      2000 * (2 * G + 1) * 97 ^ (2 * (L + G)) ≤
        4 ^ G * 22 ^ (2 * L) * 75 ^ (2 * G)) :
    400 * (4 * (Nat.choose N G) ^ 2 + 1) ≤
      Nat.choose (2 * G) G := by
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let W : ℕ := 22 ^ (2 * L) * 75 ^ (2 * G)
  have hGN : G ≤ N := by omega
  have hXpos : 0 < X := by
    dsimp [X]
    exact Nat.choose_pos hGN
  have hchoose : X * 22 ^ L * 75 ^ G ≤ 97 ^ N := by
    simpa only [X, hLG] using q6_choose_weighted_upper L G
  have hchoose2raw := Nat.pow_le_pow_left hchoose 2
  have hchoose2 : X ^ 2 * W ≤ 97 ^ (2 * N) := by
    dsimp only [W]
    calc
      X ^ 2 * (22 ^ (2 * L) * 75 ^ (2 * G)) =
          (X * 22 ^ L * 75 ^ G) ^ 2 := by
            simp only [mul_pow, ← pow_mul]
            ring
      _ ≤ (97 ^ N) ^ 2 := hchoose2raw
      _ = 97 ^ (2 * N) := by
            rw [← pow_mul]
            congr 1
            omega
  have hweighted :
      W * (2000 * (2 * G + 1) * X ^ 2) ≤ W * 4 ^ G := by
    calc
      W * (2000 * (2 * G + 1) * X ^ 2) =
          2000 * (2 * G + 1) * (X ^ 2 * W) := by ring
      _ ≤ 2000 * (2 * G + 1) * 97 ^ (2 * N) := by gcongr
      _ = 2000 * (2 * G + 1) * 97 ^ (2 * (L + G)) := by rw [hLG]
      _ ≤ 4 ^ G * 22 ^ (2 * L) * 75 ^ (2 * G) := hgap
      _ = W * 4 ^ G := by dsimp [W]; ring
  have hDX : 2000 * (2 * G + 1) * X ^ 2 ≤ 4 ^ G :=
    Nat.le_of_mul_le_mul_left hweighted (by positivity)
  have hcentral : 4 ^ G ≤ (2 * G + 1) * B := by
    simpa only [B] using Nat.four_pow_le_two_mul_add_one_mul_central_binom G
  have h2000 : 2000 * X ^ 2 ≤ B := by
    have hmul :
        (2 * G + 1) * (2000 * X ^ 2) ≤ (2 * G + 1) * B := by
      calc
        (2 * G + 1) * (2000 * X ^ 2) =
            2000 * (2 * G + 1) * X ^ 2 := by ring
        _ ≤ 4 ^ G := hDX
        _ ≤ (2 * G + 1) * B := hcentral
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hXsqPos : 0 < X ^ 2 := pow_pos hXpos 2
  have hXsq : 1 ≤ X ^ 2 := by omega
  calc
    400 * (4 * (Nat.choose N G) ^ 2 + 1) =
        400 * (4 * X ^ 2 + 1) := by rfl
    _ ≤ 400 * (5 * X ^ 2) := by omega
    _ = 2000 * X ^ 2 := by ring
    _ ≤ B := h2000
    _ = Nat.choose (2 * G) G := by rfl

/-- The profile ratio used by CW90 gives enough eventual separation between
the middle binomial coefficient and the affine hash modulus. -/
theorem solution
    (L G : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (L N + G N = N ∧ 341 * L N < 100 * G N) →
        400 * (4 * (Nat.choose N (G N)) ^ 2 + 1) ≤
          Nat.choose (2 * G N) (G N) := by
  obtain ⟨G0, hG0⟩ :=
    (eventually_atTop.1 q6_eventually_weighted_binomial_gap)
  rw [eventually_atTop]
  refine ⟨2 * G0, ?_⟩
  intro N hN hprofile
  rcases hprofile with ⟨hLG, hratio⟩
  have hGlarge : G0 ≤ G N := by omega
  exact q6_hash_modulus_le_central_of_weighted_gap hLG hratio
    (hG0 (G N) hGlarge (L N) hratio)
