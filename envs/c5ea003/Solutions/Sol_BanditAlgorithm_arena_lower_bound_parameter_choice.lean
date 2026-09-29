-- Prove2me | solution 1 for BanditAlgorithm.arena_lower_bound_parameter_choice
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:45:40.341449+00:00
-- url     : https://prove2.me/submissions/9b0b445b-2641-47df-a4b6-8229f3672708

import Mathlib
-- Ported from ryanshin accepted submission 586f03a4-1ff0-4818-afc5-2600f46ba7f1.


-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-structure-v2.lean" SHA256 d59030b33923e208f1f6162394712e529c3c534e80dd1ab815944667cf9be419

set_option autoImplicit false

namespace BanditParameterStructure

variable {S A n L d k : Nat} {D : Real}

theorem log_ratio_pos (hS : 3 <= S) (hA : 2 <= A) :
    0 < Real.log (S : Real) / Real.log (A : Real) := by
  have hS1 : (1 : Real) < S := by exact_mod_cast (show 1 < S by omega)
  have hA1 : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
  exact div_pos (Real.log_pos hS1) (Real.log_pos hA1)

theorem diameter_gt_twenty (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D) :
    20 < D := by
  have hratio := log_ratio_pos hS hA
  linarith

theorem depth_lt_log (hS : 3 <= S) (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) :
    (d : Real) < 1 + Real.log (S : Real) / Real.log (A : Real) := by
  have hA0 : (0 : Real) < A := by exact_mod_cast (show 0 < A by omega)
  have hS0 : (0 : Real) < S := by exact_mod_cast (show 0 < S by omega)
  have hA1 : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
  have hlogA : 0 < Real.log (A : Real) := Real.log_pos hA1
  have hpow : A ^ d < A * S :=
    lt_of_lt_of_le hdep (Nat.mul_le_mul_left A (Nat.sub_le S 2))
  have hpowR : (A : Real) ^ d < (A : Real) * (S : Real) := by
    exact_mod_cast hpow
  have hlog := Real.log_lt_log (pow_pos hA0 d) hpowR
  rw [Real.log_pow, Real.log_mul (ne_of_gt hA0) (ne_of_gt hS0)] at hlog
  have hdivide : (d : Real) <
      (Real.log (A : Real) + Real.log (S : Real)) / Real.log (A : Real) :=
    (lt_div_iff₀ hlogA).2 hlog
  simpa only [add_div, div_self (ne_of_gt hlogA)] using hdivide

theorem depth_lt_diameter (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hdep : A ^ d < A * (S - 2)) :
    (d : Real) < D / 20 := by
  have hdepth := depth_lt_log hS hA hdep
  linarith

theorem state_action_ge_six (hS : 3 <= S) (hA : 2 <= A) :
    6 <= S * A := by
  exact Nat.mul_le_mul hS hA

theorem family_ge_two (hA : 2 <= A) (hL1 : 1 <= L) (hk : k = L * A) :
    2 <= k := by
  rw [hk]
  exact Nat.mul_le_mul hL1 hA

theorem state_action_le_six_family (hS : 3 <= S)
    (hL : S - 2 <= 3 * L + 1) (hL1 : 1 <= L) (hk : k = L * A) :
    S * A <= 6 * k := by
  have hSL : S <= 6 * L := by omega
  calc
    S * A <= (6 * L) * A := Nat.mul_le_mul_right A hSL
    _ = 6 * k := by rw [hk]; ring

theorem scaled_diameter_le_horizon {m : Nat} (hm : m <= S * A)
    (hD0 : 0 <= D) (hn : D * (S : Real) * (A : Real) <= (n : Real)) :
    (m : Real) * D <= (n : Real) := by
  have hmR : (m : Real) <= (S : Real) * (A : Real) := by exact_mod_cast hm
  calc
    (m : Real) * D = D * (m : Real) := by ring
    _ <= D * ((S : Real) * (A : Real)) := mul_le_mul_of_nonneg_left hmR hD0
    _ = D * (S : Real) * (A : Real) := by ring
    _ <= (n : Real) := hn

theorem horizon_gt_one_twenty (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real)) :
    120 < n := by
  have hD20 := diameter_gt_twenty hS hA hD
  have hD0 : 0 <= D := by linarith
  have h6 := scaled_diameter_le_horizon (state_action_ge_six hS hA) hD0 hn
  norm_num at h6
  have h120 : (120 : Real) < n := by linarith
  exact_mod_cast h120

theorem horizon_gt_depth (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real))
    (hdep : A ^ d < A * (S - 2)) :
    120 * d < n := by
  have hD20 := diameter_gt_twenty hS hA hD
  have hD0 : 0 <= D := by linarith
  have hdepth := depth_lt_diameter hS hA hD hdep
  have h6 := scaled_diameter_le_horizon (state_action_ge_six hS hA) hD0 hn
  norm_num at h6
  have h120 : (120 : Real) * d < n := by linarith
  exact_mod_cast h120

theorem horizon_ge_two_forty (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real)) :
    240 <= n := by
  have hD20 := diameter_gt_twenty hS hA hD
  have hD0 : 0 <= D := by linarith
  by_cases hAS : A <= S
  · have hA0 : (0 : Real) < A := by exact_mod_cast (show 0 < A by omega)
    have hA1 : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
    have hlogA : 0 < Real.log (A : Real) := Real.log_pos hA1
    have hlogAS : Real.log (A : Real) <= Real.log (S : Real) :=
      Real.log_le_log hA0 (by exact_mod_cast hAS)
    have hratio : (1 : Real) <= Real.log (S : Real) / Real.log (A : Real) :=
      (le_div_iff₀ hlogA).2 (by simpa only [one_mul] using hlogAS)
    have hD40 : (40 : Real) <= D := by linarith
    have h6 := scaled_diameter_le_horizon (state_action_ge_six hS hA) hD0 hn
    norm_num at h6
    have h240 : (240 : Real) <= n := by linarith
    exact_mod_cast h240
  · have hA4 : 4 <= A := by omega
    have hSA12 : 12 <= S * A := Nat.mul_le_mul hS hA4
    have h12 := scaled_diameter_le_horizon hSA12 hD0 hn
    norm_num at h12
    have h240 : (240 : Real) <= n := by linarith
    exact_mod_cast h240

theorem states_of_depth {t : Nat} (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (ht : t + 1 <= d) :
    2 ^ t + 3 <= S := by
  have hA0 : 0 < A := by omega
  have hp : A ^ (t + 1) <= A ^ d := Nat.pow_le_pow_right hA0 ht
  have hm : A * A ^ t < A * (S - 2) := by
    simpa only [pow_succ, Nat.mul_comm] using lt_of_le_of_lt hp hdep
  have hcancel : A ^ t < S - 2 := Nat.lt_of_mul_lt_mul_left hm
  have htwo : 2 ^ t <= A ^ t := Nat.pow_le_pow_left hA t
  omega

theorem states_ge_four_of_depth_one (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (hd : 1 <= d) :
    4 <= S := by
  exact states_of_depth (t := 0) hA hdep hd

theorem states_ge_five_of_depth_two (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (hd : 2 <= d) :
    5 <= S := by
  exact states_of_depth (t := 1) hA hdep hd

theorem depth_three_data (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (hd : 3 <= d)
    (hL : S - 2 <= 3 * L + 1) (hk : k = L * A) :
    7 <= S /\ 2 <= L /\ 4 <= k /\ 14 <= S * A := by
  have hS7 : 7 <= S := states_of_depth (t := 2) hA hdep hd
  have hL2 : 2 <= L := by omega
  have hk4 : 4 <= k := by rw [hk]; exact Nat.mul_le_mul hL2 hA
  exact ⟨hS7, hL2, hk4, Nat.mul_le_mul hS7 hA⟩

theorem depth_four_data (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (hd : 4 <= d)
    (hL : S - 2 <= 3 * L + 1) (hk : k = L * A) :
    11 <= S /\ 3 <= L /\ 6 <= k /\ 22 <= S * A := by
  have hS11 : 11 <= S := states_of_depth (t := 3) hA hdep hd
  have hL3 : 3 <= L := by omega
  have hk6 : 6 <= k := by rw [hk]; exact Nat.mul_le_mul hL3 hA
  exact ⟨hS11, hL3, hk6, Nat.mul_le_mul hS11 hA⟩

theorem depth_ge_five_data (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (hd : 5 <= d)
    (hL : S - 2 <= 3 * L + 1) (hk : k = L * A) :
    19 <= S /\ 6 <= L /\ 12 <= k /\ 38 <= S * A := by
  have hS19 : 19 <= S := states_of_depth (t := 4) hA hdep hd
  have hL6 : 6 <= L := by omega
  have hk12 : 12 <= k := by rw [hk]; exact Nat.mul_le_mul hL6 hA
  exact ⟨hS19, hL6, hk12, Nat.mul_le_mul hS19 hA⟩

end BanditParameterStructure


-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-structure-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-structure-small-horizon-v1.lean" SHA256 5dcb2d46164eb72a4097594acf18c7408c8382e554df643ecb6c19d02d85ec4f

set_option autoImplicit false

namespace BanditSmallHorizon

variable {S A n d : Nat} {D : Real}

-- These private helpers keep this small gate independent of project imports.
private theorem states_lower {t : Nat} (hA : 2 <= A)
    (hdep : A ^ d < A * (S - 2)) (ht : t + 1 <= d) :
    2 ^ t + 3 <= S := by
  have hA0 : 0 < A := by omega
  have hp : A ^ (t + 1) <= A ^ d := Nat.pow_le_pow_right hA0 ht
  have hm : A * A ^ t < A * (S - 2) := by
    simpa only [pow_succ, Nat.mul_comm] using lt_of_le_of_lt hp hdep
  have hcancel : A ^ t < S - 2 := Nat.lt_of_mul_lt_mul_left hm
  have htwo : 2 ^ t <= A ^ t := Nat.pow_le_pow_left hA t
  omega

private theorem depth_diameter (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hdep : A ^ d < A * (S - 2)) :
    (d : Real) < D / 20 := by
  have hA0 : (0 : Real) < A := by exact_mod_cast (show 0 < A by omega)
  have hS0 : (0 : Real) < S := by exact_mod_cast (show 0 < S by omega)
  have hA1 : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
  have hlogA : 0 < Real.log (A : Real) := Real.log_pos hA1
  have hpow : A ^ d < A * S :=
    lt_of_lt_of_le hdep (Nat.mul_le_mul_left A (Nat.sub_le S 2))
  have hpowR : (A : Real) ^ d < (A : Real) * (S : Real) := by
    exact_mod_cast hpow
  have hlog := Real.log_lt_log (pow_pos hA0 d) hpowR
  rw [Real.log_pow, Real.log_mul (ne_of_gt hA0) (ne_of_gt hS0)] at hlog
  have hdivide : (d : Real) <
      (Real.log (A : Real) + Real.log (S : Real)) / Real.log (A : Real) :=
    (lt_div_iff₀ hlogA).2 hlog
  have hdepth : (d : Real) <
      1 + Real.log (S : Real) / Real.log (A : Real) := by
    simpa only [add_div, div_self (ne_of_gt hlogA)] using hdivide
  linarith

theorem horizon_ge_three_twenty (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real))
    (hdep : A ^ d < A * (S - 2)) (hd : 1 <= d) :
    320 <= n := by
  have hS4 : 4 <= S := states_lower (t := 0) hA hdep hd
  have hdepth := depth_diameter hS hA hD hdep
  have hdR : (1 : Real) <= d := by exact_mod_cast hd
  have hD20 : (20 : Real) < D := by linarith
  have hD0 : 0 <= D := by linarith
  by_cases hAS : A <= S
  · have hA0 : (0 : Real) < A := by exact_mod_cast (show 0 < A by omega)
    have hA1 : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
    have hlogA : 0 < Real.log (A : Real) := Real.log_pos hA1
    have hlogAS : Real.log (A : Real) <= Real.log (S : Real) :=
      Real.log_le_log hA0 (by exact_mod_cast hAS)
    have hratio : (1 : Real) <= Real.log (S : Real) / Real.log (A : Real) :=
      (le_div_iff₀ hlogA).2 (by simpa only [one_mul] using hlogAS)
    have hD40 : (40 : Real) <= D := by linarith
    have hSA8 : (8 : Real) <= (S : Real) * (A : Real) := by
      exact_mod_cast (show 8 <= S * A from Nat.mul_le_mul hS4 hA)
    have hmul := mul_le_mul_of_nonneg_left hSA8 hD0
    have hn320 : (320 : Real) <= n := by nlinarith
    exact_mod_cast hn320
  · have hA5 : 5 <= A := by omega
    have hSA20 : (20 : Real) <= (S : Real) * (A : Real) := by
      exact_mod_cast (show 20 <= S * A from Nat.mul_le_mul hS4 hA5)
    have hmul := mul_le_mul_of_nonneg_left hSA20 hD0
    have hn320 : (320 : Real) <= n := by nlinarith
    exact_mod_cast hn320

theorem horizon_ge_four_hundred (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real))
    (hdep : A ^ d < A * (S - 2)) (hd : 2 <= d) :
    400 <= n := by
  have hS5 : 5 <= S := states_lower (t := 1) hA hdep hd
  have hdepth := depth_diameter hS hA hD hdep
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hD40 : (40 : Real) < D := by linarith
  have hD0 : 0 <= D := by linarith
  have hSA10 : (10 : Real) <= (S : Real) * (A : Real) := by
    exact_mod_cast (show 10 <= S * A from Nat.mul_le_mul hS5 hA)
  have hmul := mul_le_mul_of_nonneg_left hSA10 hD0
  have hn400 : (400 : Real) <= n := by nlinarith
  exact_mod_cast hn400

theorem horizon_ge_eight_forty (hS : 3 <= S) (hA : 2 <= A)
    (hD : 20 * (1 + Real.log (S : Real) / Real.log (A : Real)) <= D)
    (hn : D * (S : Real) * (A : Real) <= (n : Real))
    (hdep : A ^ d < A * (S - 2)) (hd : 3 <= d) :
    840 <= n := by
  have hS7 : 7 <= S := states_lower (t := 2) hA hdep hd
  have hdepth := depth_diameter hS hA hD hdep
  have hdR : (3 : Real) <= d := by exact_mod_cast hd
  have hD60 : (60 : Real) < D := by linarith
  have hD0 : 0 <= D := by linarith
  have hSA14 : (14 : Real) <= (S : Real) * (A : Real) := by
    exact_mod_cast (show 14 <= S * A from Nat.mul_le_mul hS7 hA)
  have hmul := mul_le_mul_of_nonneg_left hSA14 hD0
  have hn840 : (840 : Real) <= n := by nlinarith
  exact_mod_cast hn840

end BanditSmallHorizon

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-structure-small-horizon-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-caps-v1.lean" SHA256 418f9cb26ed8a70fc0189a5ccbec53128d970acdfde2485d81188ff6a8683957

set_option autoImplicit false
noncomputable section

namespace BanditCaps

def rD (D : ℝ) (d : ℕ) : ℕ := Nat.floor (D / 4) - d - 1

def rk (k n : ℕ) : ℕ := k * n / 6000 + 1

def rn (n : ℕ) : ℕ := n / 100

def rho (D : ℝ) (d k n : ℕ) : ℕ := max 1 (min (rD D d) (min (rk k n) (rn n)))

theorem rD_cast {D : ℝ} {d : ℕ} (hD : 20 < D) (hd : (d : ℝ) < D / 20) :
    (rD D d : ℝ) = (Nat.floor (D / 4) : ℝ) - d - 1 := by
  have hD4 : 0 ≤ D / 4 := by linarith
  have hfloor : d + 1 ≤ Nat.floor (D / 4) := by
    apply (Nat.le_floor_iff hD4).mpr
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  rw [rD, Nat.sub_sub, Nat.cast_sub hfloor, Nat.cast_add, Nat.cast_one]
  ring

theorem rD_lower {D : ℝ} {d : ℕ} (hD : 20 < D) (hd : (d : ℝ) < D / 20) :
    D / 10 ≤ (rD D d : ℝ) := by
  rw [rD_cast hD hd]
  have hfloor := Nat.lt_floor_add_one (D / 4)
  linarith

theorem rD_ge_one {D : ℝ} {d : ℕ} (hD : 20 < D) (hd : (d : ℝ) < D / 20) :
    1 ≤ rD D d := by
  have h := rD_lower hD hd
  have hreal : (1 : ℝ) ≤ (rD D d : ℝ) := by linarith
  exact_mod_cast hreal

theorem rD_ge_depth {D : ℝ} {d : ℕ} (hD : 20 < D) (hd : (d : ℝ) < D / 20) :
    d ≤ rD D d := by
  have h := rD_lower hD hd
  have hreal : (d : ℝ) ≤ (rD D d : ℝ) := by linarith
  exact_mod_cast hreal

theorem rD_diameter {D : ℝ} {d : ℕ} (hD : 20 < D) (hd : (d : ℝ) < D / 20) :
    4 * ((rD D d : ℝ) + d + 1) ≤ D := by
  have hD4 : 0 ≤ D / 4 := by linarith
  have hfloor : (Nat.floor (D / 4) : ℝ) ≤ D / 4 := Nat.floor_le hD4
  rw [rD_cast hD hd]
  linarith

theorem rn_ge_one {n : ℕ} (hn : 240 ≤ n) : 1 ≤ rn n := by
  dsimp [rn]
  omega

theorem rn_ge_depth {n d : ℕ} (hdepth : 120 * d < n) : d ≤ rn n := by
  dsimp [rn]
  omega

theorem rn_mul_le (n : ℕ) : 100 * rn n ≤ n := by
  dsimp [rn]
  omega

theorem rn_lower {n : ℕ} (hn : 240 ≤ n) : (n : ℝ) / 200 ≤ (rn n : ℝ) := by
  have hquot : n < 100 * (rn n + 1) := by
    dsimp [rn]
    omega
  have hquotReal : (n : ℝ) < 100 * ((rn n : ℝ) + 1) := by exact_mod_cast hquot
  have hnReal : (240 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem rk_ge_one (k n : ℕ) : 1 ≤ rk k n := by
  dsimp [rk]
  omega

theorem rk_lower (k n : ℕ) : (k : ℝ) * n / 6000 ≤ (rk k n : ℝ) := by
  have hquot : k * n < 6000 * rk k n := by
    dsimp [rk]
    omega
  have hquotReal : (k : ℝ) * n < 6000 * (rk k n : ℝ) := by exact_mod_cast hquot
  linarith

theorem rho_ge_one (D : ℝ) (d k n : ℕ) : 1 ≤ rho D d k n := by
  exact le_max_left _ _

theorem rho_eq_min {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    rho D d k n = min (rD D d) (min (rk k n) (rn n)) := by
  apply max_eq_right
  exact le_min (rD_ge_one hD hd) (le_min (rk_ge_one k n) (rn_ge_one hn))

theorem rho_le_rD {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    rho D d k n ≤ rD D d := by
  rw [rho_eq_min (k := k) hD hd hn]
  exact min_le_left _ _

theorem rho_le_rk {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    rho D d k n ≤ rk k n := by
  rw [rho_eq_min (k := k) hD hd hn]
  exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem rho_le_rn {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    rho D d k n ≤ rn n := by
  rw [rho_eq_min (k := k) hD hd hn]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem horizon {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    100 * rho D d k n ≤ n := by
  exact le_trans (Nat.mul_le_mul_left 100 (rho_le_rn (k := k) hD hd hn)) (rn_mul_le n)

theorem diameter {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    4 * ((rho D d k n : ℝ) + d + 1) ≤ D := by
  have hcap : (rho D d k n : ℝ) ≤ (rD D d : ℝ) := by
    exact_mod_cast rho_le_rD (k := k) hD hd hn
  have hbound := rD_diameter hD hd
  linarith

theorem active_cap {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n) :
    rho D d k n = rD D d ∨ rho D d k n = rk k n ∨ rho D d k n = rn n := by
  rw [rho_eq_min (k := k) hD hd hn]
  rcases le_total (rD D d) (min (rk k n) (rn n)) with h | h
  · exact Or.inl (min_eq_left h)
  · have hm : min (rD D d) (min (rk k n) (rn n)) = min (rk k n) (rn n) := min_eq_right h
    rcases le_total (rk k n) (rn n) with hk | hn
    · exact Or.inr (Or.inl (hm.trans (min_eq_left hk)))
    · exact Or.inr (Or.inr (hm.trans (min_eq_right hn)))

theorem rho_lower {D : ℝ} {d k n : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n)
    (hk : 2 ≤ k) (hDn : 6 * D ≤ (n : ℝ)) :
    D / 500 ≤ (rho D d k n : ℝ) := by
  rcases active_cap (k := k) hD hd hn with h | h | h
  · rw [h]
    have hcap := rD_lower hD hd
    linarith
  · rw [h]
    have hcap := rk_lower k n
    have hkReal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hprod : 2 * (n : ℝ) ≤ (k : ℝ) * n :=
      mul_le_mul_of_nonneg_right hkReal (Nat.cast_nonneg n)
    linarith
  · rw [h]
    have hcap := rn_lower hn
    linarith

end BanditCaps

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-caps-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-depth-bridge-v1.lean" SHA256 5d6140b7f764e9dd0f268c1ca18a3348f135064a78ead80280f6e74b34fd5447

set_option autoImplicit false

namespace BanditDepthBridge

theorem depth_le_quotient_cap {d k n : ℕ} (hk : 12 ≤ k) (hn : 760 * d < n) :
    d ≤ k * n / 6000 + 1 := by
  have hmul : 12 * n ≤ k * n := Nat.mul_le_mul_right n hk
  omega

theorem two_le_quotient_cap {k n : ℕ} (hk : 6 ≤ k) (hn : 1760 < n) :
    2 ≤ k * n / 6000 + 1 := by
  have hmul : 6 * n ≤ k * n := Nat.mul_le_mul_right n hk
  omega

theorem depth_le_rho {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN))
    (hk : 12 ≤ k) (hn : 760 * d < n) : d ≤ rho := by
  rw [hrho]
  exact le_min hcapD (le_min (depth_le_quotient_cap hk hn) hcapN)

theorem two_le_rho_of_depth_four {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN))
    (hd : d = 4) (hk : 6 ≤ k) (hn : 1760 < n) : 2 ≤ rho := by
  rw [hrho]
  exact le_min (by omega) (le_min (two_le_quotient_cap hk hn) (by omega))

theorem depth_le_three_rho {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN)) (hpos : 1 ≤ rho)
    (hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n)
    (hfour : d = 4 → 6 ≤ k ∧ 1760 < n) : d ≤ 3 * rho := by
  by_cases hd5 : 5 ≤ d
  · rcases hlarge hd5 with ⟨hk, hn⟩
    have hdepth := depth_le_rho hcapD hcapN hrho hk hn
    omega
  · by_cases hd4 : d = 4
    · rcases hfour hd4 with ⟨hk, hn⟩
      have htwo := two_le_rho_of_depth_four hcapD hcapN hrho hd4 hk hn
      omega
    · omega

theorem depth_le_two_rho {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN)) (hpos : 2 ≤ rho)
    (hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n) : d ≤ 2 * rho := by
  by_cases hd5 : 5 ≤ d
  · rcases hlarge hd5 with ⟨hk, hn⟩
    have hdepth := depth_le_rho hcapD hcapN hrho hk hn
    omega
  · omega

theorem depth_le_rho_of_five {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN)) (hpos : 5 ≤ rho)
    (hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n) : d ≤ rho := by
  by_cases hd5 : 5 ≤ d
  · rcases hlarge hd5 with ⟨hk, hn⟩
    exact depth_le_rho hcapD hcapN hrho hk hn
  · omega

theorem depth_le_four_of_rho_le_four {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN)) (hsmall : rho ≤ 4)
    (hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n) : d ≤ 4 := by
  by_cases hd5 : 5 ≤ d
  · rcases hlarge hd5 with ⟨hk, hn⟩
    have hdepth := depth_le_rho hcapD hcapN hrho hk hn
    omega
  · omega

theorem depth_le_three_of_rho_one {d k n capD capN rho : ℕ}
    (hcapD : d ≤ capD) (hcapN : d ≤ capN)
    (hrho : rho = min capD (min (k * n / 6000 + 1) capN)) (hone : rho = 1)
    (hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n)
    (hfour : d = 4 → 6 ≤ k ∧ 1760 < n) : d ≤ 3 := by
  have hpos : 1 ≤ rho := by omega
  have hdepth := depth_le_three_rho hcapD hcapN hrho hpos hlarge hfour
  omega

theorem product_lower_of_two {rho k n : ℕ}
    (hcap : rho ≤ k * n / 6000 + 1) (hpos : 2 ≤ rho) : 3000 * rho ≤ k * n := by
  omega

theorem product_lower_of_five {rho k n : ℕ}
    (hcap : rho ≤ k * n / 6000 + 1) (hpos : 5 ≤ rho) : 4800 * rho ≤ k * n := by
  omega

theorem product_upper_of_active {rho k n : ℕ}
    (hactive : rho = k * n / 6000 + 1) : k * n < 6000 * rho := by
  omega

end BanditDepthBridge

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-depth-bridge-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-truncation-v1.lean" SHA256 8ebd50731e5d4ede55f15c1d1bb2f7c49b9d6b461290e2236db9a2c34f17a75f

set_option autoImplicit false

namespace BanditTruncation

def N (n d rho : Nat) : Nat := (n - d - 12 * rho) / (2 * rho + d)

def R (n d rho : Nat) : Nat := n - d - N n d rho * (d + 2)

variable {n d rho : Nat}

theorem denominator_pos (hrho : 1 <= rho) : 0 < 2 * rho + d := by
  omega

theorem numerator_budget (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    d + 12 * rho <= n := by
  omega

theorem numerator_add (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    (n - d - 12 * rho) + d + 12 * rho = n := by
  have hbudget := numerator_budget h100 h120
  omega

theorem thirty_le_N (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    30 <= N n d rho := by
  unfold N
  apply (Nat.le_div_iff_mul_le (denominator_pos hrho)).2
  omega

theorem N_pos (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    0 < N n d rho := by
  have h30 := thirty_le_N hrho h100 h120
  omega

theorem truncation_budget (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    d + 12 * rho + N n d rho * (2 * rho + d) <= n := by
  have hnum := numerator_add h100 h120
  have hdiv : N n d rho * (2 * rho + d) <= n - d - 12 * rho :=
    Nat.div_mul_le_self (n - d - 12 * rho) (2 * rho + d)
  omega

theorem allocation_le (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    d + N n d rho * (d + 2) <= n := by
  have hbudget := truncation_budget h100 h120
  have hden : d + 2 <= 2 * rho + d := by omega
  have hmul := Nat.mul_le_mul_left (N n d rho) hden
  omega

theorem remainder_add (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    R n d rho + d + N n d rho * (d + 2) = n := by
  have halloc := allocation_le hrho h100 h120
  unfold R
  omega

theorem remainder_lower (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    (2 * rho - 2) * N n d rho + 12 * rho <= R n d rho := by
  have hbudget := truncation_budget h100 h120
  have hrem := remainder_add hrho h100 h120
  have hsplit : 2 * rho + d = (d + 2) + (2 * rho - 2) := by omega
  have hmul : N n d rho * (2 * rho + d) =
      N n d rho * (d + 2) + (2 * rho - 2) * N n d rho := by
    rw [hsplit, Nat.mul_add]
    rw [Nat.mul_comm (N n d rho) (2 * rho - 2)]
  rw [hmul] at hbudget
  omega

theorem quotient_strict_upper (hrho : 1 <= rho) :
    n - d - 12 * rho < (N n d rho + 1) * (2 * rho + d) := by
  exact (Nat.div_lt_iff_lt_mul (denominator_pos hrho)).1
    (Nat.lt_succ_self (N n d rho))

theorem real_floor_lower (hrho : 1 <= rho)
    (h100 : 100 * rho <= n) (h120 : 120 * d < n) :
    ((n : Real) - 2 * (d : Real) - 14 * (rho : Real)) /
        (2 * (rho : Real) + (d : Real)) <= (N n d rho : Real) := by
  have hden : (0 : Real) < 2 * (rho : Real) + (d : Real) := by
    exact_mod_cast denominator_pos (d := d) hrho
  have hnum := numerator_add h100 h120
  have hnumR : ((n - d - 12 * rho : Nat) : Real) + (d : Real) +
      12 * (rho : Real) = (n : Real) := by
    exact_mod_cast hnum
  have hupper := quotient_strict_upper (n := n) (d := d) hrho
  have hupperR : ((n - d - 12 * rho : Nat) : Real) <
      ((N n d rho : Real) + 1) * (2 * (rho : Real) + (d : Real)) := by
    exact_mod_cast hupper
  apply (div_le_iff₀ hden).2
  nlinarith

end BanditTruncation

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-truncation-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-construction-v1.lean" SHA256 4a666ad649a6252df5b683bd7285367acbdffd261f9cea8f3c75e6744cb45d9c

set_option autoImplicit false

-- Concatenate after the approved structure, small-horizon, caps, depth-bridge,
-- and truncation bodies. This file intentionally has no project-local imports.
namespace BanditConstruction

theorem horizon_lt_of_active {rho n : ℕ} (hrho : 2 ≤ rho)
    (hactive : rho = BanditCaps.rn n) : n < 150 * rho := by
  unfold BanditCaps.rn at hactive
  omega

theorem rho_one_forces_product {D : ℝ} {d k n rho : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hn : 240 ≤ n)
    (hactive : rho = BanditCaps.rD D d ∨
      rho = BanditCaps.rk k n ∨ rho = BanditCaps.rn n)
    (hone : rho = 1) : rho = BanditCaps.rk k n := by
  rcases hactive with h | h | h
  · have hcap := BanditCaps.rD_lower hD hd
    rw [← h, hone] at hcap
    norm_num at hcap
    linarith
  · exact h
  · have hcap : 2 ≤ BanditCaps.rn n := by
      unfold BanditCaps.rn
      omega
    omega

theorem horizon_lt_of_product {rho k n : ℕ} (hk : 2 ≤ k)
    (hactive : rho = BanditCaps.rk k n) : n < 3000 * rho := by
  have hliteral : rho = k * n / 6000 + 1 := by
    simpa only [BanditCaps.rk] using hactive
  have hproduct := BanditDepthBridge.product_upper_of_active hliteral
  have hmul : 2 * n ≤ k * n := Nat.mul_le_mul_right n hk
  omega

theorem real_active_cap {D : ℝ} {d k n rho : ℕ}
    (hD : 20 < D) (hd : (d : ℝ) < D / 20) (hrho : 2 ≤ rho)
    (hactive : rho = BanditCaps.rD D d ∨
      rho = BanditCaps.rk k n ∨ rho = BanditCaps.rn n) :
    D ≤ 10 * (rho : ℝ) ∨
      (k : ℝ) * n < 6000 * (rho : ℝ) ∨ (n : ℝ) < 150 * (rho : ℝ) := by
  rcases hactive with h | h | h
  · have hcap := BanditCaps.rD_lower hD hd
    rw [← h] at hcap
    exact Or.inl (by linarith)
  · have hliteral : rho = k * n / 6000 + 1 := by
      simpa only [BanditCaps.rk] using h
    have hproduct := BanditDepthBridge.product_upper_of_active hliteral
    apply Or.inr
    apply Or.inl
    exact_mod_cast hproduct
  · have hhorizon := horizon_lt_of_active hrho h
    apply Or.inr
    apply Or.inr
    exact_mod_cast hhorizon

theorem size_bound {S A k rho : ℕ} {D : ℝ}
    (hD : D / 500 ≤ (rho : ℝ)) (hsize : S * A ≤ 6 * k) :
    D * ((S * A : ℕ) : ℝ) ≤ 3000 * (rho : ℝ) * k := by
  have hdiameter : D ≤ 500 * (rho : ℝ) := by linarith
  have hsizeReal : ((S * A : ℕ) : ℝ) ≤ 6 * (k : ℝ) := by
    exact_mod_cast hsize
  calc
    D * ((S * A : ℕ) : ℝ) ≤
        (500 * (rho : ℝ)) * ((S * A : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hdiameter (Nat.cast_nonneg (S * A))
    _ ≤ (500 * (rho : ℝ)) * (6 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hsizeReal (by positivity)
    _ = 3000 * (rho : ℝ) * k := by ring

structure Facts (S A n d k rho N : ℕ) (D : ℝ) : Prop where
  rho_def : rho = BanditCaps.rho D d k n
  rho_pos : 1 ≤ rho
  horizon : 100 * rho ≤ n
  depth_horizon : 120 * d < n
  horizon_ge_240 : 240 ≤ n
  family_ge_two : 2 ≤ k
  depth_le_three : d ≤ 3 * rho
  depth_le_two : 2 ≤ rho → d ≤ 2 * rho
  depth_le_of_five : 5 ≤ rho → d ≤ rho
  depth_le_four : rho ≤ 4 → d ≤ 4
  depth_le_three_of_one : rho = 1 → d ≤ 3
  N_def : N = BanditTruncation.N n d rho
  N_ge_thirty : 30 ≤ N
  N_floor : ((n : ℝ) - 2 * (d : ℝ) - 14 * (rho : ℝ)) /
      (2 * (rho : ℝ) + (d : ℝ)) ≤ (N : ℝ)
  diameter_gt_twenty : 20 < D
  depth_lt_diameter : (d : ℝ) < D / 20
  diameter : 4 * ((rho : ℝ) + d + 1) ≤ D
  six_diameter_le_horizon : 6 * D ≤ (n : ℝ)
  rho_lower : D / 500 ≤ (rho : ℝ)
  size_ge_six : 6 ≤ S * A
  size_le_six_family : S * A ≤ 6 * k
  size_rate_bound : D * ((S * A : ℕ) : ℝ) ≤ 3000 * (rho : ℝ) * k
  depth_le_diameter_cap : d ≤ BanditCaps.rD D d
  depth_le_horizon_cap : d ≤ BanditCaps.rn n
  rho_le_product_cap : rho ≤ k * n / 6000 + 1
  rho_min : rho = min (BanditCaps.rD D d)
      (min (k * n / 6000 + 1) (BanditCaps.rn n))
  active_cap : rho = BanditCaps.rD D d ∨
      rho = BanditCaps.rk k n ∨ rho = BanditCaps.rn n
  active_real_cap : 2 ≤ rho → D ≤ 10 * (rho : ℝ) ∨
      (k : ℝ) * n < 6000 * (rho : ℝ) ∨ (n : ℝ) < 150 * (rho : ℝ)
  rho_one_product_active : rho = 1 → rho = BanditCaps.rk k n
  rho_one_horizon : rho = 1 → n < 3000
  product_lower_of_two : 2 ≤ rho → 3000 * rho ≤ k * n
  product_lower_of_five : 5 ≤ rho → 4800 * rho ≤ k * n
  horizon_ge_320 : 1 ≤ d → 320 ≤ n
  horizon_ge_400 : 2 ≤ d → 400 ≤ n
  horizon_ge_840 : 3 ≤ d → 840 ≤ n
  family_ge_four_of_depth_three : 3 ≤ d → 4 ≤ k

theorem constructFacts
    (S A n L d k : ℕ) (D : ℝ)
    (hS : 3 ≤ S) (hA : 2 ≤ A)
    (hD : 20 * (1 + Real.log S / Real.log A) ≤ D)
    (hn : D * S * A ≤ (n : ℝ))
    (hdep : A ^ d < A * (S - 2)) (hL : S - 2 ≤ 3 * L + 1) (hL1 : 1 ≤ L)
    (hk : k = L * A) :
    Facts S A n d k (BanditCaps.rho D d k n)
      (BanditTruncation.N n d (BanditCaps.rho D d k n)) D := by
  let rho := BanditCaps.rho D d k n
  let N := BanditTruncation.N n d rho
  change Facts S A n d k rho N D
  have hD20 := BanditParameterStructure.diameter_gt_twenty hS hA hD
  have hD0 : 0 ≤ D := by linarith
  have hdD := BanditParameterStructure.depth_lt_diameter hS hA hD hdep
  have hn240 := BanditParameterStructure.horizon_ge_two_forty hS hA hD hn
  have h120 := BanditParameterStructure.horizon_gt_depth hS hA hD hn hdep
  have hk2 := BanditParameterStructure.family_ge_two hA hL1 hk
  have hsize6 := BanditParameterStructure.state_action_ge_six hS hA
  have hsizek := BanditParameterStructure.state_action_le_six_family hS hL hL1 hk
  have h6D := BanditParameterStructure.scaled_diameter_le_horizon hsize6 hD0 hn
  norm_num at h6D
  have hrho : 1 ≤ rho := BanditCaps.rho_ge_one D d k n
  have h100 : 100 * rho ≤ n := BanditCaps.horizon (k := k) hD20 hdD hn240
  have hcapD := BanditCaps.rD_ge_depth hD20 hdD
  have hcapN := BanditCaps.rn_ge_depth h120
  have hmin : rho = min (BanditCaps.rD D d)
      (min (k * n / 6000 + 1) (BanditCaps.rn n)) := by
    simpa only [BanditCaps.rk] using
      (BanditCaps.rho_eq_min (d := d) (k := k) (n := n) hD20 hdD hn240)
  have hcapK : rho ≤ k * n / 6000 + 1 := by
    simpa only [BanditCaps.rk] using
      (BanditCaps.rho_le_rk (d := d) (k := k) (n := n) hD20 hdD hn240)
  have hactive : rho = BanditCaps.rD D d ∨
      rho = BanditCaps.rk k n ∨ rho = BanditCaps.rn n :=
    BanditCaps.active_cap (k := k) hD20 hdD hn240
  have hlarge : 5 ≤ d → 12 ≤ k ∧ 760 * d < n := by
    intro hd5
    rcases BanditParameterStructure.depth_ge_five_data hA hdep hd5 hL hk with
      ⟨_, _, hk12, hsize38⟩
    have h38D :=
      BanditParameterStructure.scaled_diameter_le_horizon hsize38 hD0 hn
    norm_num at h38D
    have h760Real : (760 : ℝ) * d < (n : ℝ) := by linarith
    have h760 : 760 * d < n := by exact_mod_cast h760Real
    exact ⟨hk12, h760⟩
  have hfour : d = 4 → 6 ≤ k ∧ 1760 < n := by
    intro hd4
    rcases BanditParameterStructure.depth_four_data hA hdep (by omega) hL hk with
      ⟨_, _, hk6, hsize22⟩
    have h22D :=
      BanditParameterStructure.scaled_diameter_le_horizon hsize22 hD0 hn
    norm_num at h22D
    have hd4Real : (d : ℝ) = 4 := by exact_mod_cast hd4
    have h1760Real : (1760 : ℝ) < (n : ℝ) := by linarith
    have h1760 : 1760 < n := by exact_mod_cast h1760Real
    exact ⟨hk6, h1760⟩
  have hdepth3 :=
    BanditDepthBridge.depth_le_three_rho hcapD hcapN hmin hrho hlarge hfour
  have hrhoLower : D / 500 ≤ (rho : ℝ) :=
    BanditCaps.rho_lower (k := k) hD20 hdD hn240 hk2 h6D
  have honeActive : rho = 1 → rho = BanditCaps.rk k n :=
    rho_one_forces_product hD20 hdD hn240 hactive
  have honeHorizon : rho = 1 → n < 3000 := by
    intro hone
    have hsmall := horizon_lt_of_product hk2 (honeActive hone)
    omega
  refine {
    rho_def := rfl
    rho_pos := hrho
    horizon := h100
    depth_horizon := h120
    horizon_ge_240 := hn240
    family_ge_two := hk2
    depth_le_three := hdepth3
    depth_le_two := fun htwo =>
      BanditDepthBridge.depth_le_two_rho hcapD hcapN hmin htwo hlarge
    depth_le_of_five := fun hfive =>
      BanditDepthBridge.depth_le_rho_of_five hcapD hcapN hmin hfive hlarge
    depth_le_four := fun hsmall =>
      BanditDepthBridge.depth_le_four_of_rho_le_four hcapD hcapN hmin hsmall hlarge
    depth_le_three_of_one := fun hone =>
      BanditDepthBridge.depth_le_three_of_rho_one hcapD hcapN hmin hone hlarge hfour
    N_def := rfl
    N_ge_thirty := BanditTruncation.thirty_le_N hrho h100 h120
    N_floor := BanditTruncation.real_floor_lower hrho h100 h120
    diameter_gt_twenty := hD20
    depth_lt_diameter := hdD
    diameter := BanditCaps.diameter (k := k) hD20 hdD hn240
    six_diameter_le_horizon := h6D
    rho_lower := hrhoLower
    size_ge_six := hsize6
    size_le_six_family := hsizek
    size_rate_bound := size_bound hrhoLower hsizek
    depth_le_diameter_cap := hcapD
    depth_le_horizon_cap := hcapN
    rho_le_product_cap := hcapK
    rho_min := hmin
    active_cap := hactive
    active_real_cap := fun htwo => real_active_cap hD20 hdD htwo hactive
    rho_one_product_active := honeActive
    rho_one_horizon := honeHorizon
    product_lower_of_two := fun htwo =>
      BanditDepthBridge.product_lower_of_two hcapK htwo
    product_lower_of_five := fun hfive =>
      BanditDepthBridge.product_lower_of_five hcapK hfive
    horizon_ge_320 := fun hd1 =>
      BanditSmallHorizon.horizon_ge_three_twenty hS hA hD hn hdep hd1
    horizon_ge_400 := fun hd2 =>
      BanditSmallHorizon.horizon_ge_four_hundred hS hA hD hn hdep hd2
    horizon_ge_840 := fun hd3 =>
      BanditSmallHorizon.horizon_ge_eight_forty hS hA hD hn hdep hd3
    family_ge_four_of_depth_three := ?_
  }
  intro hd3
  exact (BanditParameterStructure.depth_three_data hA hdep hd3 hL hk).2.2.1

end BanditConstruction

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-construction-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-calibration-v3.lean" SHA256 f207ceadc10051223c62ffeae3d2eb3f2f1702c260938143040da33ee2cb9369

set_option autoImplicit false
noncomputable section

namespace BanditParameterCalibration

def Dsc (n N : ℝ) : ℝ := n / N

def c3 (n N rho : ℝ) : ℝ := rho * N / n

def c2 (n N c k Delta : ℝ) : ℝ :=
  c ^ 2 * (k - 1) ^ 2 * Dsc n N / (8 * Delta ^ 2 * n * k)

theorem Dsc_pos {n N : ℝ} (hn : 0 < n) (hN : 0 < N) :
    0 < Dsc n N := by
  exact div_pos hn hN

theorem c3_pos {n N rho : ℝ} (hn : 0 < n) (hN : 0 < N) (hrho : 0 < rho) :
    0 < c3 n N rho := by
  exact div_pos (mul_pos hrho hN) hn

theorem c2_pos {n N c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) :
    0 < c2 n N c k Delta := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  dsimp [c2, Dsc]
  positivity

theorem c2_eq {n N c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hk : 1 < k) (hDelta : 0 < Delta) :
    c2 n N c k Delta = c ^ 2 * (k - 1) ^ 2 / (8 * Delta ^ 2 * N * k) := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  dsimp [c2, Dsc]
  field_simp [ne_of_gt hn, ne_of_gt hN, ne_of_gt hkpos, ne_of_gt hDelta]

theorem calibration_radicand_eq {n N c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) :
    Dsc n N / (2 * c2 n N c k Delta * n * k) =
      (2 * Delta / (c * (k - 1))) ^ 2 := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  dsimp [c2, Dsc]
  field_simp [ne_of_gt hn, ne_of_gt hN, ne_of_gt hc, ne_of_gt hkpos,
    ne_of_gt hkm, ne_of_gt hDelta]
  ring

theorem calibration {n N c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) :
    Delta = c * (k - 1) / 2 * Real.sqrt (Dsc n N / (2 * c2 n N c k Delta * n * k)) := by
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  rw [calibration_radicand_eq hn hN hc hk hDelta, Real.sqrt_sq (by positivity)]
  field_simp [ne_of_gt hc, ne_of_gt hkm]

theorem gain_radicand_eq {n N c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) :
    Dsc n N * k * n / (2 * c2 n N c k Delta) =
      (2 * Delta * n * k / (c * (k - 1))) ^ 2 := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  dsimp [c2, Dsc]
  field_simp [ne_of_gt hn, ne_of_gt hN, ne_of_gt hc, ne_of_gt hkpos,
    ne_of_gt hkm, ne_of_gt hDelta]
  ring

theorem net_identity {n N rho c k Delta : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hrho : 0 < rho)
    (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) :
    c ^ 2 * c3 n N rho / 16 * Real.sqrt (Dsc n N * k * n / (2 * c2 n N c k Delta)) -
        (1 / 2 + Delta) / (1 / rho) =
      rho * (c * N * Delta * k / (8 * (k - 1)) - 1 / 2 - Delta) := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  rw [gain_radicand_eq hn hN hc hk hDelta, Real.sqrt_sq (by positivity)]
  dsimp [c3]
  field_simp [ne_of_gt hn, ne_of_gt hrho, ne_of_gt hc, ne_of_gt hkm]
  ring

theorem c2_lower_of_delta_le {n N rho c k Delta lambda : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hrho : 0 < rho)
    (hc : 0 < c) (hk : 1 < k) (hDelta : 0 < Delta) (hlambda : 0 < lambda)
    (hcap : Delta ≤ c * (k - 1) / 2 * Real.sqrt (lambda / (2 * k * (n + rho)))) :
    (n + rho) / (lambda * N) ≤ c2 n N c k Delta := by
  have hkpos : 0 < k := lt_trans zero_lt_one hk
  have hkm : 0 < k - 1 := sub_pos.mpr hk
  have hsum : 0 < n + rho := add_pos hn hrho
  have hrad : 0 ≤ lambda / (2 * k * (n + rho)) := by positivity
  have hsq : Delta ^ 2 ≤ c ^ 2 * (k - 1) ^ 2 * lambda / (8 * k * (n + rho)) := by
    calc
      Delta ^ 2 ≤ (c * (k - 1) / 2 * Real.sqrt (lambda / (2 * k * (n + rho)))) ^ 2 :=
        (sq_le_sq₀ (le_of_lt hDelta) (by positivity)).mpr hcap
      _ = c ^ 2 * (k - 1) ^ 2 * lambda / (8 * k * (n + rho)) := by
        rw [mul_pow, Real.sq_sqrt hrad]
        field_simp [ne_of_gt hkpos, ne_of_gt hsum]
        ring
  have hden : 0 < 8 * k * (n + rho) := by positivity
  have hcross : Delta ^ 2 * (8 * k * (n + rho)) ≤ c ^ 2 * (k - 1) ^ 2 * lambda :=
    (le_div_iff₀ hden).mp hsq
  rw [c2_eq hn hN hk hDelta]
  apply (div_le_div_iff₀ (mul_pos hlambda hN) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_right hcross (le_of_lt hN) using 1 <;> ring

end BanditParameterCalibration

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-variant-audit-bandit-calibration-v3.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-unsaturated-v2.lean" SHA256 839feea09e79cef4254f72a369add0b1cf700ed2a9c3c8621cf9382858209473

set_option autoImplicit false

noncomputable section

namespace BanditUnsaturated

def c : Real := 63 / 64

def deltaMax (rho n k d : Real) : Real :=
  c * (k - 1) / 2 * Real.sqrt ((rho + d + 1) / (2 * k * (n + rho)))

def gain (rho n k N d : Real) : Real :=
  rho * c ^ 2 * N / 16 * Real.sqrt ((rho + d + 1) * k / (2 * (n + rho)))

def net (rho k N Delta : Real) : Real :=
  rho * (c * N * Delta * k / (8 * (k - 1)) - 1 / 2 - Delta)

def mainTerm (rho n k N d : Real) : Real :=
  rho * c / 2 * (c * N / 8 - 1) *
    Real.sqrt ((rho + d + 1) * k / (2 * (n + rho)))

theorem root_identity (rho n k d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 0 < k) (hd : 0 <= d) :
    Real.sqrt ((rho + d + 1) * k / (2 * (n + rho))) =
      k * Real.sqrt ((rho + d + 1) / (2 * k * (n + rho))) := by
  have hsum : 0 < n + rho := add_pos hn hrho
  have hrad : 0 <= (rho + d + 1) / (2 * k * (n + rho)) := by positivity
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  rw [mul_pow, Real.sq_sqrt hrad]
  field_simp [ne_of_gt hk, ne_of_gt hsum]

theorem deltaMax_pos (rho n k d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 1 < k) (hd : 0 <= d) :
    0 < deltaMax rho n k d := by
  unfold deltaMax c
  have hkm : 0 < k - 1 := by linarith
  positivity

theorem net_at_max (rho n k N d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 1 < k) (hd : 0 <= d) :
    net rho k N (deltaMax rho n k d) =
      gain rho n k N d - rho * (1 / 2 + deltaMax rho n k d) := by
  have hroot := root_identity rho n k d hrho hn (by linarith) hd
  have hkm : k - 1 ≠ 0 := ne_of_gt (by linarith)
  unfold net gain deltaMax
  rw [hroot]
  field_simp [hkm]
  ring

theorem gain_minus_delta (rho n k N d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 0 < k) (hd : 0 <= d) :
    gain rho n k N d - rho * deltaMax rho n k d =
      mainTerm rho n k N d +
        rho * c / 2 * Real.sqrt ((rho + d + 1) / (2 * k * (n + rho))) := by
  have hroot := root_identity rho n k d hrho hn hk hd
  unfold gain deltaMax mainTerm
  rw [hroot]
  ring

theorem net_ge_main (rho n k N d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 1 < k) (hd : 0 <= d) :
    mainTerm rho n k N d - rho / 2 <= net rho k N (deltaMax rho n k d) := by
  have hgain := gain_minus_delta rho n k N d hrho hn (by linarith) hd
  have hextra : 0 <= rho * c / 2 *
      Real.sqrt ((rho + d + 1) / (2 * k * (n + rho))) := by
    unfold c
    positivity
  rw [net_at_max rho n k N d hrho hn hk hd]
  linarith only [hgain, hextra]

theorem large_rate (rho n k D s M : Real)
    (hrho : 0 <= rho) (hn : 0 <= n) (hk : 0 <= k)
    (hD : 0 <= D) (hs : 0 <= s)
    (hkn : 4800 * rho <= k * n) (hsize : D * s <= 3000 * rho * k)
    (hmain : (3 / 250 : Real) * Real.sqrt (rho * n * k) <= M) :
    Real.sqrt (D * s * n) / 12500 <= M - rho / 2 := by
  have hscale : 0 <= rho * n * k := by positivity
  have htarget : 0 <= D * s * n := by positivity
  have hknScaled := mul_le_mul_of_nonneg_left hkn hrho
  have hlossSq : (rho / 2) ^ 2 <=
      ((3 / 400 : Real) * Real.sqrt (rho * n * k)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hscale]
    nlinarith only [hknScaled, sq_nonneg rho]
  have hloss : rho / 2 <= (3 / 400 : Real) * Real.sqrt (rho * n * k) :=
    (sq_le_sq₀ (by positivity) (by positivity)).1 hlossSq
  have hsizeScaled := mul_le_mul_of_nonneg_right hsize hn
  have htargetSq : (Real.sqrt (D * s * n)) ^ 2 <=
      (55 * Real.sqrt (rho * n * k)) ^ 2 := by
    rw [Real.sq_sqrt htarget, mul_pow, Real.sq_sqrt hscale]
    nlinarith only [hsizeScaled, hscale]
  have htargetRoot : Real.sqrt (D * s * n) <= 55 * Real.sqrt (rho * n * k) :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1 htargetSq
  have hrootNonneg := Real.sqrt_nonneg (rho * n * k)
  linarith only [hmain, hloss, htargetRoot, hrootNonneg]

end BanditUnsaturated

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-unsaturated-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-feasibility-v1.lean" SHA256 e99f09ad7f0c8e62691c881665b6311b4a9e145e3b472369d2b631f02a4b5f91

/- Uncompiled feasibility bridge. Calibration and the tail estimate are premises;
   the final lower-rate inequality is deliberately absent. -/

set_option autoImplicit false

noncomputable section

namespace BanditFeasibility

def c : Real := 63 / 64

def restart (rho : Real) (hrho : 1 <= rho) : NNReal :=
  ⟨1 / rho, (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hrho)).le⟩

def advantage (Delta : Real) (hDelta : 0 < Delta) : NNReal :=
  ⟨Delta, hDelta.le⟩

def Dsc (n N : Nat) : Real := (n : Real) / (N : Real)

def c3 (n N : Nat) (rho : Real) : Real := rho * (N : Real) / (n : Real)

theorem restart_coe (rho : Real) (hrho : 1 <= rho) :
    ((restart rho hrho : NNReal) : Real) = 1 / rho := rfl

theorem advantage_coe (Delta : Real) (hDelta : 0 < Delta) :
    ((advantage Delta hDelta : NNReal) : Real) = Delta := rfl

theorem restart_reciprocal (rho : Real) (hrho : 1 <= rho) :
    1 / ((restart rho hrho : NNReal) : Real) = rho := by
  change 1 / (1 / rho) = rho
  exact one_div_one_div rho

theorem restart_le_one (rho : Real) (hrho : 1 <= rho) :
    restart rho hrho <= 1 := by
  have hpos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  change (1 : Real) / rho <= 1
  apply (div_le_iff₀ hpos).2
  simpa only [one_mul] using hrho

theorem horizon_div_scale (n N : Nat) (hn : 0 < n) :
    (n : Real) / Dsc n N = (N : Real) := by
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  unfold Dsc
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (ne_of_gt hnReal)]

theorem scale_product (n N : Nat) (rho : Real) (hn : 0 < n) (hN : 0 < N) :
    c3 n N rho * Dsc n N = rho := by
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  have hNReal : 0 < (N : Real) := Nat.cast_pos'.2 hN
  unfold c3 Dsc
  rw [← mul_div_assoc, div_mul_cancel₀ _ (ne_of_gt hnReal),
    mul_div_cancel_right₀ _ (ne_of_gt hNReal)]

def Constraints (n d k N : Nat) (D : Real) (delta Delta : NNReal)
    (epsilon c1 c2 c3 Dsc : Real) : Prop :=
  delta <= 1 ∧ (0 : Real) < delta ∧ Delta <= 1 / 4 ∧ Delta <= 1 / 2 ∧
  2 <= k ∧ 0 < n ∧ 0 < N ∧ 0 < Dsc ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
  (N : Real) <= (n : Real) / Dsc ∧ c3 * Dsc <= 1 / (delta : Real) ∧
  c1 * (n : Real) / Dsc <= (1 - epsilon) * (N : Real) ∧
  ((n : Real) + 1 / (delta : Real)) / (1 / (delta : Real) + (d : Real) + 1) <=
    c2 * (n : Real) / Dsc ∧
  d + N * (d + 2) <= n ∧
  (2 : Real) ^ N <= epsilon * (1 + (delta : Real)) ^ N *
    (1 + (delta : Real) / 2) ^ (n - d - N * (d + 2)) ∧
  (Delta : Real) = c1 * ((k : Real) - 1) / 2 *
    Real.sqrt (Dsc / (2 * c2 * (n : Real) * (k : Real))) ∧
  4 * (1 / (delta : Real) + (d : Real) + 1) <= D

theorem constraints (n d k N : Nat) (rho Delta C2 D : Real)
    (hrho : 1 <= rho) (hN : 30 <= N) (hk : 2 <= k) (hn : 0 < n)
    (hDelta : 0 < Delta) (hcap : Delta <= 1 / 4) (hC2 : 0 < C2)
    (hC2lower : ((n : Real) + rho) / ((rho + (d : Real) + 1) * (N : Real)) <= C2)
    (hcalibration : Delta = c * ((k : Real) - 1) / 2 *
      Real.sqrt (Dsc n N / (2 * C2 * (n : Real) * (k : Real))))
    (hbudget : d + N * (d + 2) <= n)
    (htail : (2 : Real) ^ N <= (1 / 64) * (1 + 1 / rho) ^ N *
      (1 + (1 / rho) / 2) ^ (n - d - N * (d + 2)))
    (hdiameter : 4 * (rho + (d : Real) + 1) <= D) :
    Constraints n d k N D (restart rho hrho) (advantage Delta hDelta)
      (1 / 64) c C2 (c3 n N rho) (Dsc n N) := by
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hNPos : 0 < N := lt_of_lt_of_le (by decide : 0 < 30) hN
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  have hNReal : 0 < (N : Real) := Nat.cast_pos'.2 hNPos
  have hdeltaPos : (0 : Real) < (restart rho hrho : NNReal) :=
    one_div_pos.mpr hrhoPos
  have hDeltaQuarter : advantage Delta hDelta <= 1 / 4 := by
    change Delta <= (1 / 4 : Real)
    exact hcap
  have hDeltaHalf : advantage Delta hDelta <= 1 / 2 := by
    change Delta <= (1 / 2 : Real)
    linarith only [hcap]
  have hDscPos : 0 < Dsc n N := div_pos hnReal hNReal
  have hcPos : 0 < c := by norm_num [c]
  have hc3Pos : 0 < c3 n N rho := div_pos (mul_pos hrhoPos hNReal) hnReal
  have hcount : ((n : Real) + rho) / (rho + (d : Real) + 1) <= C2 * (N : Real) := by
    apply (div_le_iff₀ hNReal).1
    simpa only [div_div] using hC2lower
  unfold Constraints
  refine ⟨restart_le_one rho hrho, hdeltaPos, hDeltaQuarter, hDeltaHalf,
    hk, hn, hNPos, hDscPos, hcPos, hC2, hc3Pos, ?_, ?_, ?_, ?_, hbudget, ?_, ?_, ?_⟩
  · exact le_of_eq (horizon_div_scale n N hn).symm
  · exact le_of_eq ((scale_product n N rho hn hNPos).trans
      (restart_reciprocal rho hrho).symm)
  · rw [mul_div_assoc, horizon_div_scale n N hn]
    norm_num [c]
  · simpa only [restart_reciprocal, mul_div_assoc, horizon_div_scale n N hn] using hcount
  · simpa only [restart_coe] using htail
  · simpa only [advantage_coe] using hcalibration
  · simpa only [restart_reciprocal] using hdiameter

end BanditFeasibility

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-feasibility-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-calibration-feasibility-v1.lean" SHA256 7c4f9101ad3668be7bbf563c8df10bc5a6e1001bad9bd0fc342edf63835e40be
/- Uncompiled dependent body. Requires BanditParameterCalibration,
   BanditUnsaturated, and BanditFeasibility from their reviewed source bodies.
   The existential conclusion retains the rate bound as an explicit premise. -/

set_option autoImplicit false

noncomputable section

namespace BanditWitnessAssembly

def chosenDelta (n d k : Nat) (rho : Real) : Real :=
  min (1 / 4) (BanditUnsaturated.deltaMax rho (n : Real) (k : Real) (d : Real))

def chosenC2 (n d k N : Nat) (rho : Real) : Real :=
  BanditParameterCalibration.c2 (n : Real) (N : Real) BanditFeasibility.c
    (k : Real) (chosenDelta n d k rho)

theorem chosenDelta_pos (n d k : Nat) (rho : Real)
    (hrho : 1 <= rho) (hk : 2 <= k) (hn : 0 < n) :
    0 < chosenDelta n d k rho := by
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  have hkNat : 1 < k := lt_of_lt_of_le (by decide : 1 < 2) hk
  have hkReal : (1 : Real) < (k : Real) := by
    simpa only [Nat.cast_one] using (Nat.cast_lt (α := Real)).2 hkNat
  unfold chosenDelta
  exact lt_min (by norm_num)
    (BanditUnsaturated.deltaMax_pos rho (n : Real) (k : Real) (d : Real)
      hrhoPos hnReal hkReal (Nat.cast_nonneg d))

theorem calibrated_constraints (n d k N : Nat) (rho D : Real)
    (hrho : 1 <= rho) (hN : 30 <= N) (hk : 2 <= k) (hn : 0 < n)
    (hbudget : d + N * (d + 2) <= n)
    (htail : (2 : Real) ^ N <= (1 / 64) * (1 + 1 / rho) ^ N *
      (1 + (1 / rho) / 2) ^ (n - d - N * (d + 2)))
    (hdiameter : 4 * (rho + (d : Real) + 1) <= D) :
    BanditFeasibility.Constraints n d k N D
      (BanditFeasibility.restart rho hrho)
      (BanditFeasibility.advantage (chosenDelta n d k rho)
        (chosenDelta_pos n d k rho hrho hk hn))
      (1 / 64) BanditFeasibility.c (chosenC2 n d k N rho)
      (BanditFeasibility.c3 n N rho) (BanditFeasibility.Dsc n N) := by
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  have hNPos : 0 < N := lt_of_lt_of_le (by decide : 0 < 30) hN
  have hNReal : 0 < (N : Real) := Nat.cast_pos'.2 hNPos
  have hkNat : 1 < k := lt_of_lt_of_le (by decide : 1 < 2) hk
  have hkReal : (1 : Real) < (k : Real) := by
    simpa only [Nat.cast_one] using (Nat.cast_lt (α := Real)).2 hkNat
  have hc : 0 < BanditFeasibility.c := by norm_num [BanditFeasibility.c]
  have hDelta := chosenDelta_pos n d k rho hrho hk hn
  have hlambda : 0 < rho + (d : Real) + 1 := by positivity
  have hcap : chosenDelta n d k rho <= (1 / 4 : Real) := min_le_left _ _
  have hmax : chosenDelta n d k rho <=
      BanditFeasibility.c * ((k : Real) - 1) / 2 *
        Real.sqrt ((rho + (d : Real) + 1) / (2 * (k : Real) * ((n : Real) + rho))) :=
    min_le_right _ _
  refine BanditFeasibility.constraints n d k N rho (chosenDelta n d k rho)
    (chosenC2 n d k N rho) D hrho hN hk hn hDelta hcap ?_ ?_ ?_
    hbudget htail hdiameter
  · unfold chosenC2
    exact BanditParameterCalibration.c2_pos hnReal hNReal hc hkReal hDelta
  · unfold chosenC2
    exact BanditParameterCalibration.c2_lower_of_delta_le
      hnReal hNReal hrhoPos hc hkReal hDelta hlambda hmax
  · unfold chosenC2
    exact BanditParameterCalibration.calibration hnReal hNReal hc hkReal hDelta

theorem calibrated_net (n d k N : Nat) (rho : Real)
    (hrho : 1 <= rho) (hN : 30 <= N) (hk : 2 <= k) (hn : 0 < n) :
    BanditFeasibility.c ^ 2 * BanditFeasibility.c3 n N rho / 16 *
        Real.sqrt (BanditFeasibility.Dsc n N * (k : Real) * (n : Real) /
          (2 * chosenC2 n d k N rho)) -
        (1 / 2 + ((BanditFeasibility.advantage (chosenDelta n d k rho)
          (chosenDelta_pos n d k rho hrho hk hn) : NNReal) : Real)) /
          ((BanditFeasibility.restart rho hrho : NNReal) : Real) =
      BanditUnsaturated.net rho (k : Real) (N : Real) (chosenDelta n d k rho) := by
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hnReal : 0 < (n : Real) := Nat.cast_pos'.2 hn
  have hNPos : 0 < N := lt_of_lt_of_le (by decide : 0 < 30) hN
  have hNReal : 0 < (N : Real) := Nat.cast_pos'.2 hNPos
  have hkNat : 1 < k := lt_of_lt_of_le (by decide : 1 < 2) hk
  have hkReal : (1 : Real) < (k : Real) := by
    simpa only [Nat.cast_one] using (Nat.cast_lt (α := Real)).2 hkNat
  have hc : 0 < BanditFeasibility.c := by norm_num [BanditFeasibility.c]
  have hDelta := chosenDelta_pos n d k rho hrho hk hn
  have h := BanditParameterCalibration.net_identity hnReal hNReal hrhoPos hc hkReal hDelta
  simpa only [chosenC2, BanditFeasibility.c3, BanditFeasibility.Dsc,
    BanditFeasibility.restart_coe, BanditFeasibility.advantage_coe,
    BanditParameterCalibration.c3, BanditParameterCalibration.Dsc,
    BanditUnsaturated.net, BanditUnsaturated.c, BanditFeasibility.c] using h

theorem exists_parameters_of_net_rate (S A n d k N : Nat) (rho D : Real)
    (hrho : 1 <= rho) (hN : 30 <= N) (hk : 2 <= k) (hn : 0 < n)
    (hbudget : d + N * (d + 2) <= n)
    (htail : (2 : Real) ^ N <= (1 / 64) * (1 + 1 / rho) ^ N *
      (1 + (1 / rho) / 2) ^ (n - d - N * (d + 2)))
    (hdiameter : 4 * (rho + (d : Real) + 1) <= D)
    (hrate : (1 / 12500 : Real) * Real.sqrt (D * (S : Real) * (A : Real) * (n : Real)) <=
      BanditUnsaturated.net rho (k : Real) (N : Real) (chosenDelta n d k rho)) :
    ∃ (delta Delta : NNReal) (N' : Nat) (epsilon c1 c2 c3 Dsc : Real),
      delta <= 1 ∧ (0 : Real) < delta ∧ Delta <= 1 / 4 ∧ Delta <= 1 / 2 ∧
      2 <= k ∧ 0 < n ∧ 0 < N' ∧ 0 < Dsc ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      (N' : Real) <= (n : Real) / Dsc ∧ c3 * Dsc <= 1 / (delta : Real) ∧
      c1 * (n : Real) / Dsc <= (1 - epsilon) * (N' : Real) ∧
      ((n : Real) + 1 / (delta : Real)) / (1 / (delta : Real) + (d : Real) + 1) <=
        c2 * (n : Real) / Dsc ∧
      d + N' * (d + 2) <= n ∧
      (2 : Real) ^ N' <= epsilon * (1 + (delta : Real)) ^ N' *
        (1 + (delta : Real) / 2) ^ (n - d - N' * (d + 2)) ∧
      (Delta : Real) = c1 * ((k : Real) - 1) / 2 *
        Real.sqrt (Dsc / (2 * c2 * (n : Real) * (k : Real))) ∧
      4 * (1 / (delta : Real) + (d : Real) + 1) <= D ∧
      (1 / 12500 : Real) * Real.sqrt (D * (S : Real) * (A : Real) * (n : Real)) <=
        c1 ^ 2 * c3 / 16 * Real.sqrt (Dsc * (k : Real) * (n : Real) / (2 * c2)) -
          (1 / 2 + (Delta : Real)) / (delta : Real) := by
  refine ⟨BanditFeasibility.restart rho hrho,
    BanditFeasibility.advantage (chosenDelta n d k rho) (chosenDelta_pos n d k rho hrho hk hn),
    N, 1 / 64, BanditFeasibility.c, chosenC2 n d k N rho,
    BanditFeasibility.c3 n N rho, BanditFeasibility.Dsc n N, ?_⟩
  have hfeasible := calibrated_constraints n d k N rho D hrho hN hk hn
    hbudget htail hdiameter
  have hnet := calibrated_net n d k N rho hrho hN hk hn
  have hfinal := hrate.trans (le_of_eq hnet.symm)
  simpa only [BanditFeasibility.Constraints, and_assoc] using And.intro hfeasible hfinal

end BanditWitnessAssembly

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-calibration-feasibility-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-rho-v1.lean" SHA256 2425583e357a229db6fb3e5fe108f33f0aea1ac4ac74db86307c0188d1eff825

/- Uncompiled finite coefficient certificates, independent of the full target. -/

set_option autoImplicit false

noncomputable section

namespace BanditFiniteRho

def coefficient (rho d n : Real) : Real :=
  (1 - (2 * d + 14 * rho) / n) * Real.sqrt (rho * (rho + d + 1)) /
    (2 * rho + d)

private theorem coefficient_of_cell (rho d n0 n : Real)
    (hrho : 0 < rho) (hd : 0 <= d) (hn0 : 0 < n0) (hn : n0 <= n)
    (hpart : 0 <= 1 - (2 * d + 14 * rho) / n0)
    (hcell : (43 / 100 : Real) ^ 2 * (2 * rho + d) ^ 2 <=
      (1 - (2 * d + 14 * rho) / n0) ^ 2 * rho * (rho + d + 1)) :
    43 / 100 <= coefficient rho d n := by
  have hden : 0 < 2 * rho + d := by linarith
  have hrad : 0 <= rho * (rho + d + 1) := by positivity
  have hleft : 0 <= (43 / 100 : Real) * (2 * rho + d) := by positivity
  have hright : 0 <=
      (1 - (2 * d + 14 * rho) / n0) * Real.sqrt (rho * (rho + d + 1)) :=
    mul_nonneg hpart (Real.sqrt_nonneg _)
  have hsq : ((43 / 100 : Real) * (2 * rho + d)) ^ 2 <=
      ((1 - (2 * d + 14 * rho) / n0) *
        Real.sqrt (rho * (rho + d + 1))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hrad]
    simpa only [mul_assoc] using hcell
  have hroot := (sq_le_sq₀ hleft hright).mp hsq
  have hbase : 43 / 100 <= coefficient rho d n0 := by
    unfold coefficient
    exact (le_div_iff₀ hden).2 hroot
  have hfrac : (2 * d + 14 * rho) / n <= (2 * d + 14 * rho) / n0 :=
    div_le_div_of_nonneg_left (by positivity) hn0 hn
  have hpartle := sub_le_sub_left hfrac 1
  have hprod := mul_le_mul_of_nonneg_right hpartle
    (Real.sqrt_nonneg (rho * (rho + d + 1)))
  have hmono : coefficient rho d n0 <= coefficient rho d n := by
    unfold coefficient
    exact div_le_div_of_nonneg_right hprod hden.le
  exact hbase.trans hmono

theorem coefficient_lower (rho d : Nat) (n : Real)
    (hrhoLow : 2 <= rho) (hrhoHigh : rho <= 4) (hd : d <= 4)
    (h100 : 100 * (rho : Real) <= n) (h120 : 120 * (d : Real) <= n) :
    43 / 100 <= coefficient (rho : Real) (d : Real) n := by
  have hrho : 0 < (rho : Real) :=
    Nat.cast_pos'.2 (lt_of_lt_of_le (by decide : 0 < 2) hrhoLow)
  refine coefficient_of_cell (rho : Real) (d : Real)
    (max (100 * (rho : Real)) (120 * (d : Real))) n hrho
    (Nat.cast_nonneg d) ?_ (max_le h100 h120) ?_ ?_
  · exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : Real) < 100) hrho)
      (le_max_left _ _)
  · interval_cases rho <;> interval_cases d <;> norm_num
  · interval_cases rho <;> interval_cases d <;> norm_num

theorem coefficient_sq_lower (rho d : Nat) (n : Real)
    (hrhoLow : 2 <= rho) (hrhoHigh : rho <= 4) (hd : d <= 4)
    (h100 : 100 * (rho : Real) <= n) (h120 : 120 * (d : Real) <= n) :
    (43 / 100 : Real) ^ 2 <= (coefficient (rho : Real) (d : Real) n) ^ 2 := by
  have h := coefficient_lower rho d n hrhoLow hrhoHigh hd h100 h120
  have hnonneg : 0 <= coefficient (rho : Real) (d : Real) n :=
    (by norm_num : (0 : Real) <= 43 / 100).trans h
  exact (sq_le_sq₀ (by norm_num) hnonneg).2 h

end BanditFiniteRho

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-rho-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-gain-v2.lean" SHA256 9312300d5fdb3e2262632cf1f6c461524dfa10a9062e48bc9f4195b467e7c287

/- Uncompiled gain assembly; the finite coefficient estimate is a hypothesis. -/

set_option autoImplicit false

noncomputable section

namespace BanditFiniteGain

def c : Real := 63 / 64

def gain (n N rho d k : Real) : Real :=
  rho * c ^ 2 * N / 16 * Real.sqrt ((rho + d + 1) * k / (2 * (n + rho)))

def scale (rho k n : Real) : Real := Real.sqrt (rho * k * n)

private theorem coefficient_product (n N rho d : Real)
    (hn : 0 < n) (hrho : 0 < rho) (hd : 0 <= d)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N)
    (hg : 43 / 100 <=
      (1 - (2 * d + 14 * rho) / n) * Real.sqrt (rho * (rho + d + 1)) /
        (2 * rho + d)) :
    (43 / 100) * n <= N * Real.sqrt (rho * (rho + d + 1)) := by
  have hden : 0 < 2 * rho + d := by linarith
  have hidentity :
      (1 - (2 * d + 14 * rho) / n) * Real.sqrt (rho * (rho + d + 1)) /
          (2 * rho + d) =
        ((n - 2 * d - 14 * rho) / (2 * rho + d)) *
          (Real.sqrt (rho * (rho + d + 1)) / n) := by
    field_simp [ne_of_gt hn, ne_of_gt hden]
    ring
  rw [hidentity] at hg
  have hmono := mul_le_mul_of_nonneg_right hfloor
    (div_nonneg (Real.sqrt_nonneg (rho * (rho + d + 1))) hn.le)
  have hratio : 43 / 100 <= N * Real.sqrt (rho * (rho + d + 1)) / n := by
    simpa only [mul_div_assoc] using hg.trans hmono
  exact (le_div_iff₀ hn).1 hratio

theorem gain_lower_bound (n N rho d k : Real)
    (hrho : 0 < rho) (hd : 0 <= d) (hN : 0 <= N) (hk : 0 < k)
    (hhorizon : 100 * rho <= n)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N)
    (hg : 43 / 100 <=
      (1 - (2 * d + 14 * rho) / n) * Real.sqrt (rho * (rho + d + 1)) /
        (2 * rho + d)) :
    scale rho k n / Real.sqrt 3000 <= gain n N rho d k := by
  have hn : 0 < n := by linarith
  have hsum : 0 < n + rho := add_pos hn hrho
  have hlambda : 0 < rho + d + 1 := by linarith
  have hprod := coefficient_product n N rho d hn hrho hd hfloor hg
  have hrad : 0 <= rho * (rho + d + 1) := mul_nonneg hrho.le hlambda.le
  have hsqprod : (43 / 100 : Real) ^ 2 * n ^ 2 <=
      N ^ 2 * rho * (rho + d + 1) := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hprod
    rw [mul_pow, mul_pow, Real.sq_sqrt hrad] at hs
    simpa only [mul_assoc] using hs
  have hconstant : 512 * (101 / 100 : Real) <=
      3000 * c ^ 4 * (43 / 100) ^ 2 := by norm_num [c]
  have hhn := mul_le_mul_of_nonneg_left hhorizon hn.le
  have hcore : 512 * n * (n + rho) <=
      3000 * c ^ 4 * (N ^ 2 * rho * (rho + d + 1)) := by
    calc
      512 * n * (n + rho) <= (512 * (101 / 100)) * n ^ 2 := by
        nlinarith only [hhn]
      _ <= (3000 * c ^ 4 * (43 / 100) ^ 2) * n ^ 2 :=
        mul_le_mul_of_nonneg_right hconstant (sq_nonneg n)
      _ = (3000 * c ^ 4) * ((43 / 100) ^ 2 * n ^ 2) := by ring
      _ <= 3000 * c ^ 4 * (N ^ 2 * rho * (rho + d + 1)) :=
        mul_le_mul_of_nonneg_left hsqprod (by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hcore (mul_nonneg hrho.le hk.le)
  have hgainrad : 0 <= (rho + d + 1) * k / (2 * (n + rho)) := by positivity
  have hscaleRad : 0 <= rho * k * n := by positivity
  have hsquare : (scale rho k n / Real.sqrt 3000) ^ 2 <=
      (gain n N rho d k) ^ 2 := by
    rw [scale, div_pow, Real.sq_sqrt hscaleRad,
      Real.sq_sqrt (by norm_num : (0 : Real) <= 3000)]
    rw [gain, mul_pow, Real.sq_sqrt hgainrad, ← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 2) hsum)).2
    nlinarith only [hscaled]
  have hleft : 0 <= scale rho k n / Real.sqrt 3000 := by
    unfold scale
    positivity
  have hright : 0 <= gain n N rho d k := by
    unfold gain
    positivity
  exact (sq_le_sq₀ hleft hright).1 hsquare

theorem scale_div_sqrt_ge_rho (rho k n : Real)
    (hrho : 0 <= rho) (hk : 0 <= k) (hn : 0 <= n)
    (hkn : 3000 * rho <= k * n) :
    rho <= scale rho k n / Real.sqrt 3000 := by
  have hscaled := mul_le_mul_of_nonneg_left hkn hrho
  have hrad : 0 <= rho * k * n := by positivity
  have hsquare : (rho * Real.sqrt 3000) ^ 2 <= (scale rho k n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) <= 3000),
      scale, Real.sq_sqrt hrad]
    nlinarith only [hscaled]
  have hproduct : rho * Real.sqrt 3000 <= scale rho k n :=
    (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1 hsquare
  exact (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 3000))).2 hproduct

theorem gain_ge_rho (n N rho d k : Real)
    (hrho : 0 < rho) (hd : 0 <= d) (hN : 0 <= N) (hk : 0 < k)
    (hhorizon : 100 * rho <= n) (hkn : 3000 * rho <= k * n)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N)
    (hg : 43 / 100 <=
      (1 - (2 * d + 14 * rho) / n) * Real.sqrt (rho * (rho + d + 1)) /
        (2 * rho + d)) :
    rho <= gain n N rho d k := by
  have hn : 0 <= n := by linarith
  exact (scale_div_sqrt_ge_rho rho k n hrho.le hk.le hn hkn).trans
    (gain_lower_bound n N rho d k hrho hd hN hk hhorizon hfloor hg)

end BanditFiniteGain

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-gain-v2.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-net-v1.lean" SHA256 ce07c2a6b6956a65bd70090a46e4b9fe012b374e6ed3af65e0ef22cb364fd11f

/- Uncompiled loss and active-cap comparisons; the gain bounds are hypotheses. -/

set_option autoImplicit false

noncomputable section

namespace BanditFiniteNet

def net (M rho Delta : Real) : Real := M - rho * (1 / 2 + Delta)

def target (D s n : Real) : Real := Real.sqrt (D * s * n) / 12500

theorem net_quarters (M rho Delta : Real)
    (hrho : 0 <= rho) (hM : rho <= M) (hDelta : Delta <= 1 / 4) :
    M / 4 <= net M rho Delta ∧ rho / 4 <= net M rho Delta := by
  have hsum : 1 / 2 + Delta <= (3 / 4 : Real) := by linarith only [hDelta]
  have hloss := mul_le_mul_of_nonneg_left hsum hrho
  unfold net
  constructor <;> linarith only [hM, hloss]

theorem target_le_horizon (D s n : Real)
    (hD : 0 <= D) (hs : 0 <= s) (hn : 0 <= n) (hbudget : D * s <= n) :
    target D s n <= n / 12500 := by
  have hrad : 0 <= D * s * n := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbudget hn
  have hsquare : (Real.sqrt (D * s * n)) ^ 2 <= n ^ 2 := by
    rw [Real.sq_sqrt hrad]
    nlinarith only [hmul]
  have hroot := (sq_le_sq₀ (Real.sqrt_nonneg _) hn).1 hsquare
  exact div_le_div_of_nonneg_right hroot (by norm_num)

theorem scale_le_fifty_five_gain (M rho k n : Real)
    (hgain : Real.sqrt (rho * k * n) / Real.sqrt 3000 <= M) :
    Real.sqrt (rho * k * n) <= 55 * M := by
  have hden : 0 < Real.sqrt (3000 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hM : 0 <= M := (div_nonneg (Real.sqrt_nonneg _) hden.le).trans hgain
  have hbound : Real.sqrt (3000 : Real) <= 55 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : Real) <= 55)).1
    rw [Real.sq_sqrt (by norm_num : (0 : Real) <= 3000)]
    norm_num
  have hcross := (div_le_iff₀ hden).1 hgain
  have hmul := mul_le_mul_of_nonneg_left hbound hM
  nlinarith only [hcross, hmul]

theorem diameter_cap (M rho Delta D s n k : Real)
    (hrho : 0 <= rho) (hD : 0 <= D) (hs : 0 <= s)
    (hn : 0 <= n) (hk : 0 <= k)
    (hM : rho <= M) (hDelta : Delta <= 1 / 4)
    (hgain : Real.sqrt (rho * k * n) / Real.sqrt 3000 <= M)
    (hdiameter : D <= 10 * rho) (hsize : s <= 6 * k) :
    target D s n <= net M rho Delta := by
  have hrad : 0 <= D * s * n := by positivity
  have hscaleRad : 0 <= rho * k * n := by positivity
  have hprod := mul_le_mul hdiameter hsize hs (by positivity : 0 <= 10 * rho)
  have hscaled := mul_le_mul_of_nonneg_right hprod hn
  have hsquare : (Real.sqrt (D * s * n)) ^ 2 <=
      (8 * Real.sqrt (rho * k * n)) ^ 2 := by
    rw [Real.sq_sqrt hrad, mul_pow, Real.sq_sqrt hscaleRad]
    nlinarith only [hscaled, hscaleRad]
  have hroot : Real.sqrt (D * s * n) <= 8 * Real.sqrt (rho * k * n) :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1 hsquare
  have hscale := scale_le_fifty_five_gain M rho k n hgain
  have hMnonneg : 0 <= M := hrho.trans hM
  have htarget : target D s n <= M / 4 := by
    unfold target
    linarith only [hroot, hscale, hMnonneg]
  exact htarget.trans (net_quarters M rho Delta hrho hM hDelta).1

private theorem target_le_net_of_horizon (M rho Delta D s n : Real)
    (hrho : 0 <= rho) (hD : 0 <= D) (hs : 0 <= s) (hn : 0 <= n)
    (hM : rho <= M) (hDelta : Delta <= 1 / 4)
    (hbudget : D * s <= n) (hsmall : n <= 3000 * rho) :
    target D s n <= net M rho Delta := by
  have hquarter : n / 12500 <= rho / 4 := by linarith only [hsmall, hrho]
  exact (target_le_horizon D s n hD hs hn hbudget).trans
    (hquarter.trans (net_quarters M rho Delta hrho hM hDelta).2)

theorem count_cap (M rho Delta D s n k : Real)
    (hrho : 0 <= rho) (hD : 0 <= D) (hs : 0 <= s) (hn : 0 <= n)
    (hk : 2 <= k) (hM : rho <= M) (hDelta : Delta <= 1 / 4)
    (hbudget : D * s <= n) (hcount : k * n < 6000 * rho) :
    target D s n <= net M rho Delta := by
  have hmul := mul_le_mul_of_nonneg_right hk hn
  have hsmall : n <= 3000 * rho := by linarith only [hcount, hmul]
  exact target_le_net_of_horizon M rho Delta D s n hrho hD hs hn hM hDelta
    hbudget hsmall

theorem horizon_cap (M rho Delta D s n : Real)
    (hrho : 0 <= rho) (hD : 0 <= D) (hs : 0 <= s) (hn : 0 <= n)
    (hM : rho <= M) (hDelta : Delta <= 1 / 4)
    (hbudget : D * s <= n) (hhorizon : n < 150 * rho) :
    target D s n <= net M rho Delta := by
  have hsmall : n <= 3000 * rho := by linarith only [hhorizon, hrho]
  exact target_le_net_of_horizon M rho Delta D s n hrho hD hs hn hM hDelta
    hbudget hsmall

end BanditFiniteNet

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-finite-net-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-saturated-v1.lean" SHA256 a57a7712f244e5e69083cebdd5e87b32ec3dce955c2cb04dbea793db225cb9e0

/- Uncompiled saturated scalar bound; no claim of the complete target. -/

set_option autoImplicit false

noncomputable section

namespace BanditSaturated

def c : Real := 63 / 64

theorem truncation_mass_lower (n N rho d : Real)
    (hrho : 0 < rho) (hd : 0 <= d) (hN : 0 <= N)
    (hdepth : d <= 3 * rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N) :
    4 * n / 25 <= rho * N := by
  have hden : 0 < 2 * rho + d := by linarith
  have hcross : n - 2 * d - 14 * rho <= N * (2 * rho + d) :=
    (div_le_iff₀ hden).1 hfloor
  have hnum : 4 * n / 5 <= n - 2 * d - 14 * rho := by
    linarith only [hdepth, hhorizon]
  have hdenle : 2 * rho + d <= 5 * rho := by linarith only [hdepth]
  have hupper := mul_le_mul_of_nonneg_left hdenle hN
  nlinarith only [hnum, hcross, hupper]

theorem saturated_bound (n N rho d k : Real)
    (hrho : 0 < rho) (hd : 0 <= d) (hN : 30 <= N) (hk : 2 <= k)
    (hdepth : d <= 3 * rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N) :
    n / 1250 <=
      rho * (c * N * (1 / 4) * k / (8 * (k - 1)) - 1 / 2 - 1 / 4) := by
  have hNnonneg : 0 <= N := (by norm_num : (0 : Real) <= 30).trans hN
  have hmass := truncation_mass_lower n N rho d hrho hd hNnonneg
    hdepth hhorizon hfloor
  have hkpos : 0 < k - 1 := by linarith only [hk]
  have hcoef : 0 <= c * N := mul_nonneg (by norm_num [c]) hNnonneg
  have hmain : c * N / 32 <= c * N * (1 / 4) * k / (8 * (k - 1)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 8) hkpos)).2
    nlinarith only [hcoef]
  have hlinear : N / 200 <= c * N / 32 - 3 / 4 := by
    unfold c
    linarith only [hN]
  have hbracket : N / 200 <=
      c * N * (1 / 4) * k / (8 * (k - 1)) - 1 / 2 - 1 / 4 := by
    linarith only [hlinear, hmain]
  have hscaled := mul_le_mul_of_nonneg_left hbracket hrho.le
  nlinarith only [hmass, hscaled]

end BanditSaturated

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-saturated-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-large-rho-v1.lean" SHA256 b6f3008b81fd1b72800f9f9b8037fdefbe84844332ff46802f0fb007b5de1232

set_option autoImplicit false

noncomputable section

namespace BanditLargeRho

def c : Real := 63 / 64

def mainTerm (rho n k N d : Real) : Real :=
  rho * c / 2 * (c * N / 8 - 1) *
    Real.sqrt ((rho + d + 1) * k / (2 * (n + rho)))

theorem mass_square_lower (rho n N d : Real)
    (hrho : 0 < rho) (hn : 0 <= n) (hN : 0 <= N) (hd : 0 <= d)
    (hdepth : d <= rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N) :
    (98 / 625 : Real) * n ^ 2 <= rho * N ^ 2 * (rho + d + 1) := by
  have hden : 0 < 2 * rho + d := by linarith
  have hcross := (div_le_iff₀ hden).1 hfloor
  have hnum : 21 * n / 25 <= n - 2 * d - 14 * rho := by
    linarith only [hdepth, hhorizon]
  have hnd : 21 * n / 25 <= N * (2 * rho + d) := hnum.trans hcross
  have hsq := (sq_le_sq₀ (show 0 <= 21 * n / 25 by positivity)
    (mul_nonneg hN hden.le)).2 hnd
  have hdenSq : (2 * rho + d) ^ 2 <= (9 / 2 : Real) * rho * (rho + d) := by
    have hp := mul_nonneg (sub_nonneg.mpr hdepth) (show 0 <= rho + 2 * d by positivity)
    nlinarith only [hp]
  have hprod := mul_le_mul_of_nonneg_left hdenSq (sq_nonneg N)
  have hextra := mul_nonneg hrho.le (sq_nonneg N)
  nlinarith only [hsq, hprod, hextra]

theorem main_lower (rho n k N d : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 0 <= k) (hN : 30 <= N) (hd : 0 <= d)
    (hdepth : d <= rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N) :
    (3 / 250 : Real) * Real.sqrt (rho * n * k) <= mainTerm rho n k N d := by
  have hN0 : 0 <= N := by linarith
  have hsum : 0 < n + rho := add_pos hn hrho
  have hc : 0 < c := by norm_num [c]
  have hrad : 0 <= (rho + d + 1) * k / (2 * (n + rho)) := by positivity
  have hcore := mass_square_lower rho n N d hrho hn.le hN0 hd hdepth hhorizon hfloor
  let C : Real := c ^ 2 * 689 ^ 2 / (8 * 7680 ^ 2)
  let Q : Real := rho * c / 2 * ((689 / 7680 : Real) * N) *
    Real.sqrt ((rho + d + 1) * k / (2 * (n + rho)))
  have hC : 0 <= C := by norm_num [C, c]
  have hQ : 0 <= Q := by dsimp [Q]; positivity
  have hQsq : Q ^ 2 = C * rho * k * (rho * N ^ 2 * (rho + d + 1)) / (n + rho) := by
    dsimp [Q, C]
    simp only [mul_pow, div_pow, Real.sq_sqrt hrad]
    field_simp [ne_of_gt hsum]
    ring
  have hratio : (100 / 101 : Real) * n <= n ^ 2 / (n + rho) := by
    apply (le_div_iff₀ hsum).2
    have hp := mul_le_mul_of_nonneg_left hhorizon hn.le
    nlinarith only [hp]
  have hconstant : (9 / 62500 : Real) <= C * (98 / 625) * (100 / 101) := by
    norm_num [C, c]
  have hsq : ((3 / 250 : Real) * Real.sqrt (rho * n * k)) ^ 2 <= Q ^ 2 := by
    calc
      ((3 / 250 : Real) * Real.sqrt (rho * n * k)) ^ 2 =
          (9 / 62500 : Real) * (rho * n * k) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      _ <= (C * (98 / 625) * (100 / 101)) * (rho * n * k) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = (C * rho * k * (98 / 625)) * ((100 / 101) * n) := by ring
      _ <= (C * rho * k * (98 / 625)) * (n ^ 2 / (n + rho)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = C * rho * k * ((98 / 625) * n ^ 2) / (n + rho) := by ring
      _ <= C * rho * k * (rho * N ^ 2 * (rho + d + 1)) / (n + rho) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcore (by positivity)) hsum.le
      _ = Q ^ 2 := hQsq.symm
  have hroot := (sq_le_sq₀ (show 0 <= (3 / 250 : Real) * Real.sqrt (rho * n * k) by positivity) hQ).1 hsq
  have hB : (689 / 7680 : Real) * N <= c * N / 8 - 1 := by
    unfold c
    linarith only [hN]
  have hmul := mul_le_mul_of_nonneg_left hB (show 0 <= rho * c / 2 by positivity)
  have hmain := mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg ((rho + d + 1) * k / (2 * (n + rho))))
  exact hroot.trans hmain

end BanditLargeRho

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-large-rho-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-rate-branches-v1.lean" SHA256 ea8dcec7f893c7dcdd2964442a546ff065629f8aeeb61517d28674356c4b6df7

set_option autoImplicit false

noncomputable section

namespace BanditRateBranches

theorem saturated (rho n k N d D s : Real)
    (hrho : 0 < rho) (hn : 0 <= n) (hk : 2 <= k) (hN : 30 <= N) (hd : 0 <= d)
    (hD : 0 <= D) (hs : 0 <= s) (hbudget : D * s <= n)
    (hdepth : d <= 3 * rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N) :
    Real.sqrt (D * s * n) / 12500 <= BanditUnsaturated.net rho k N (1 / 4) := by
  have htarget : Real.sqrt (D * s * n) / 12500 <= n / 12500 :=
    BanditFiniteNet.target_le_horizon D s n hD hs hn hbudget
  have hsmall : n / 12500 <= n / 1250 := by linarith only [hn]
  exact htarget.trans (hsmall.trans
    (BanditSaturated.saturated_bound n N rho d k hrho hd hN hk hdepth hhorizon hfloor))

theorem large (rho n k N d D s : Real)
    (hrho : 0 < rho) (hn : 0 < n) (hk : 2 <= k) (hN : 30 <= N) (hd : 0 <= d)
    (hD : 0 <= D) (hs : 0 <= s)
    (hdepth : d <= rho) (hhorizon : rho <= n / 100)
    (hfloor : (n - 2 * d - 14 * rho) / (2 * rho + d) <= N)
    (hkn : 4800 * rho <= k * n) (hsize : D * s <= 3000 * rho * k) :
    Real.sqrt (D * s * n) / 12500 <=
      BanditUnsaturated.net rho k N (BanditUnsaturated.deltaMax rho n k d) := by
  have hk0 : 0 <= k := by linarith only [hk]
  have hmain : (3 / 250 : Real) * Real.sqrt (rho * n * k) <=
      BanditUnsaturated.mainTerm rho n k N d :=
    BanditLargeRho.main_lower rho n k N d hrho hn hk0 hN hd hdepth hhorizon hfloor
  have hrate := BanditUnsaturated.large_rate rho n k D s
    (BanditUnsaturated.mainTerm rho n k N d) hrho.le hn.le hk0 hD hs hkn hsize hmain
  exact hrate.trans (BanditUnsaturated.net_ge_main rho n k N d hrho hn (by linarith only [hk]) hd)

theorem finite (rho d : Nat) (n k N D s : Real)
    (hrho2 : 2 <= rho) (hrho4 : rho <= 4) (hd4 : d <= 4)
    (hk : 2 <= k) (hN : 30 <= N) (hD : 0 <= D) (hs : 0 <= s)
    (hbudget : D * s <= n) (h100 : 100 * (rho : Real) <= n)
    (h120 : 120 * (d : Real) <= n)
    (hfloor : (n - 2 * (d : Real) - 14 * (rho : Real)) /
      (2 * (rho : Real) + (d : Real)) <= N)
    (hkn : 3000 * (rho : Real) <= k * n)
    (hsize : s <= 6 * k)
    (hcaps : D <= 10 * (rho : Real) ∨ k * n < 6000 * (rho : Real) ∨ n < 150 * (rho : Real))
    (hDelta : BanditUnsaturated.deltaMax (rho : Real) n k (d : Real) <= 1 / 4) :
    Real.sqrt (D * s * n) / 12500 <=
      BanditUnsaturated.net (rho : Real) k N
        (BanditUnsaturated.deltaMax (rho : Real) n k (d : Real)) := by
  have hrho : 0 < (rho : Real) := by exact_mod_cast (show 0 < rho by omega)
  have hn : 0 < n := by linarith only [hrho, h100]
  have hk0 : 0 < k := by linarith only [hk]
  have hN0 : 0 <= N := by linarith only [hN]
  have hd : 0 <= (d : Real) := Nat.cast_nonneg d
  have hg := BanditFiniteRho.coefficient_lower rho d n hrho2 hrho4 hd4 h100 h120
  let M : Real := BanditFiniteGain.gain n N (rho : Real) (d : Real) k
  have hgain : Real.sqrt ((rho : Real) * k * n) / Real.sqrt 3000 <= M :=
    BanditFiniteGain.gain_lower_bound n N (rho : Real) (d : Real) k
      hrho hd hN0 hk0 h100 hfloor hg
  have hM : (rho : Real) <= M :=
    BanditFiniteGain.gain_ge_rho n N (rho : Real) (d : Real) k
      hrho hd hN0 hk0 h100 hkn hfloor hg
  rw [BanditUnsaturated.net_at_max (rho : Real) n k N (d : Real)
    hrho hn (by linarith only [hk]) hd]
  change BanditFiniteNet.target D s n <=
    BanditFiniteNet.net M (rho : Real) (BanditUnsaturated.deltaMax (rho : Real) n k (d : Real))
  rcases hcaps with hcap | hcap | hcap
  · exact BanditFiniteNet.diameter_cap M (rho : Real)
      (BanditUnsaturated.deltaMax (rho : Real) n k (d : Real)) D s n k
      hrho.le hD hs hn.le hk0.le hM hDelta hgain hcap hsize
  · exact BanditFiniteNet.count_cap M (rho : Real)
      (BanditUnsaturated.deltaMax (rho : Real) n k (d : Real)) D s n k
      hrho.le hD hs hn.le hk hM hDelta hbudget hcap
  · exact BanditFiniteNet.horizon_cap M (rho : Real)
      (BanditUnsaturated.deltaMax (rho : Real) n k (d : Real)) D s n
      hrho.le hD hs hn.le hM hDelta hbudget hcap

end BanditRateBranches

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-rate-branches-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-small-rho-v1.lean" SHA256 925e37d28ffe86c230f7657526cb4b8a8be915150f3bd92da8ad6c9f03b22e03

/- Uncompiled scalar certificates only; no claim of the complete target. -/

set_option autoImplicit false

noncomputable section

namespace BanditSmallRho

def c : Real := 63 / 64

def lowerBound (d n : Real) : Real :=
  (c ^ 2 * (n - 2 * d - 14) - 4 * c * (d + 2)) /
    (16 * Real.sqrt ((d + 2) * (n + 1))) - 1 / 2

private def offset (d : Real) : Real :=
  c ^ 2 * (2 * d + 14) + 4 * c * (d + 2)

private def coeffA (d : Real) : Real :=
  c ^ 4 - 256 * (d + 2) * (3001 / 12500 ^ 2 + 1 / 12500)

private def coeffB (d : Real) : Real :=
  2 * c ^ 2 * offset d + 256 * (d + 2) * (1 / 4 + 1 / 12500)

private def coeffC (d : Real) : Real :=
  offset d ^ 2 - 64 * (d + 2)

private def quadratic (d n : Real) : Real :=
  coeffA d * n ^ 2 - coeffB d * n + coeffC d

private theorem certificate_of_quadratic (d n0 n : Real)
    (hd : 0 < d + 2) (hn0 : 0 <= n0) (hn : n0 <= n) (hmax : n <= 3000)
    (hA : 0 <= coeffA d) (hQ : 0 <= quadratic d n0)
    (hslope : 0 <= 2 * coeffA d * n0 - coeffB d)
    (hnum0 : 0 <= c ^ 2 * n0 - offset d) :
    n / 12500 <= lowerBound d n := by
  have hnnonneg : 0 <= n := hn0.trans hn
  have hstep : 0 <= n - n0 := sub_nonneg.mpr hn
  have hquadratic : 0 <= quadratic d n := by
    calc
      0 <= quadratic d n0 +
          (2 * coeffA d * n0 - coeffB d) * (n - n0) +
          coeffA d * (n - n0) ^ 2 :=
        add_nonneg (add_nonneg hQ (mul_nonneg hslope hstep))
          (mul_nonneg hA (sq_nonneg _))
      _ = quadratic d n := by unfold quadratic; ring
  have htail : 0 <=
      (256 * (d + 2) / 12500 ^ 2) * n ^ 2 * (3000 - n) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (sq_nonneg n)) (sub_nonneg.mpr hmax)
  have hpoly : 0 <=
      (c ^ 2 * n - offset d) ^ 2 -
        256 * (d + 2) * (n + 1) * (1 / 2 + n / 12500) ^ 2 := by
    calc
      0 <= quadratic d n +
          (256 * (d + 2) / 12500 ^ 2) * n ^ 2 * (3000 - n) :=
        add_nonneg hquadratic htail
      _ = (c ^ 2 * n - offset d) ^ 2 -
          256 * (d + 2) * (n + 1) * (1 / 2 + n / 12500) ^ 2 := by
        unfold quadratic coeffA coeffB coeffC
        ring
  have hnum : 0 <= c ^ 2 * n - offset d := by
    have hinc := mul_nonneg (sq_nonneg c) hstep
    nlinarith only [hnum0, hinc]
  have hrad : 0 < (d + 2) * (n + 1) :=
    mul_pos hd (by linarith)
  have hsqrt : 0 < Real.sqrt ((d + 2) * (n + 1)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 < 16 * Real.sqrt ((d + 2) * (n + 1)) := by positivity
  have hleft : 0 <=
      16 * Real.sqrt ((d + 2) * (n + 1)) * (1 / 2 + n / 12500) := by
    positivity
  have hsq :
      (16 * Real.sqrt ((d + 2) * (n + 1)) * (1 / 2 + n / 12500)) ^ 2 <=
        (c ^ 2 * n - offset d) ^ 2 := by
    calc
      (16 * Real.sqrt ((d + 2) * (n + 1)) * (1 / 2 + n / 12500)) ^ 2 =
          256 * (d + 2) * (n + 1) * (1 / 2 + n / 12500) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hrad.le]
        ring
      _ <= (c ^ 2 * n - offset d) ^ 2 := by linarith only [hpoly]
  have hproduct := (sq_le_sq₀ hleft hnum).mp hsq
  have hdiv : 1 / 2 + n / 12500 <=
      (c ^ 2 * n - offset d) /
        (16 * Real.sqrt ((d + 2) * (n + 1))) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using hproduct
  have hidentity : c ^ 2 * n - offset d =
      c ^ 2 * (n - 2 * d - 14) - 4 * c * (d + 2) := by
    unfold offset
    ring
  rw [hidentity] at hdiv
  unfold lowerBound
  linarith only [hdiv]

theorem rho_one_depth_zero (n : Real) (hn : 240 <= n) (hmax : n <= 3000) :
    n / 12500 <= lowerBound 0 n := by
  apply certificate_of_quadratic 0 240 n (by norm_num) (by norm_num) hn hmax
  all_goals norm_num [coeffA, coeffB, coeffC, quadratic, offset, c]

theorem rho_one_depth_one (n : Real) (hn : 320 <= n) (hmax : n <= 3000) :
    n / 12500 <= lowerBound 1 n := by
  apply certificate_of_quadratic 1 320 n (by norm_num) (by norm_num) hn hmax
  all_goals norm_num [coeffA, coeffB, coeffC, quadratic, offset, c]

theorem rho_one_depth_two (n : Real) (hn : 400 <= n) (hmax : n <= 3000) :
    n / 12500 <= lowerBound 2 n := by
  apply certificate_of_quadratic 2 400 n (by norm_num) (by norm_num) hn hmax
  all_goals norm_num [coeffA, coeffB, coeffC, quadratic, offset, c]

theorem rho_one_depth_three (n : Real) (hn : 840 <= n) (hmax : n <= 3000) :
    n / 12500 <= lowerBound 3 n := by
  apply certificate_of_quadratic 3 840 n (by norm_num) (by norm_num) hn hmax
  all_goals norm_num [coeffA, coeffB, coeffC, quadratic, offset, c]

end BanditSmallRho

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-final-pipeline-bandit-small-rho-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-rho-one-bridge-v1.lean" SHA256 6f73e738377d87aacaddf5709bac3fc8ae6750c841acb7d791702d567d325e51

set_option autoImplicit false

noncomputable section

namespace BanditRhoOneBridge

def c : Real := 63 / 64

def net (d n N k : Real) : Real :=
  c / 2 * Real.sqrt ((d + 2) / (2 * (n + 1))) *
    ((c * N / 8 - 1) * Real.sqrt k + 1 / Real.sqrt k) - 1 / 2

def lowerBound (d n : Real) : Real :=
  (c ^ 2 * (n - 2 * d - 14) - 4 * c * (d + 2)) /
    (16 * Real.sqrt ((d + 2) * (n + 1))) - 1 / 2

theorem weighted_reciprocal_mono (B u v : Real)
    (hB : 1 <= B) (hv : 1 <= v) (hu : v <= u) :
    B * v + 1 / v <= B * u + 1 / u := by
  have hv0 : 0 < v := by linarith
  have hu1 : 1 <= u := hv.trans hu
  have hu0 : 0 < u := by linarith
  have hmul := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv)
  have huv : 1 <= u * v := by nlinarith only [hmul, hu1, hv]
  have hrecip : 1 / (u * v) <= (1 : Real) :=
    (div_le_one (mul_pos hu0 hv0)).2 huv
  have hfactor : 0 <= B - 1 / (u * v) := by linarith
  have hproduct := mul_nonneg (sub_nonneg.mpr hu) hfactor
  have hidentity :
      B * u + 1 / u - (B * v + 1 / v) =
        (u - v) * (B - 1 / (u * v)) := by
    field_simp [ne_of_gt hu0, ne_of_gt hv0]
    ring
  linarith only [hproduct, hidentity]

theorem sqrt_weighted_reciprocal_le (B k : Real)
    (hB : 1 <= B) (hk : 2 <= k) :
    B * Real.sqrt 2 + 1 / Real.sqrt 2 <=
      B * Real.sqrt k + 1 / Real.sqrt k := by
  apply weighted_reciprocal_mono B (Real.sqrt k) (Real.sqrt 2) hB
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact Real.sqrt_le_sqrt hk

theorem radical_identity (h r : Real) (hh : 0 < h) (hr : 0 < r) :
    Real.sqrt (h / (2 * r)) * Real.sqrt 2 =
      h / Real.sqrt (h * r) := by
  have hroot : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have rroot : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have troot : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  calc
    Real.sqrt (h / (2 * r)) * Real.sqrt 2 =
        (Real.sqrt h / (Real.sqrt 2 * Real.sqrt r)) * Real.sqrt 2 := by
      rw [Real.sqrt_div hh.le, Real.sqrt_mul (show (0 : Real) <= 2 by norm_num)]
    _ = Real.sqrt h / Real.sqrt r := by
      field_simp [ne_of_gt rroot, ne_of_gt troot]
    _ = h / (Real.sqrt h * Real.sqrt r) := by
      apply (div_eq_div_iff (ne_of_gt rroot)
        (mul_ne_zero (ne_of_gt hroot) (ne_of_gt rroot))).2
      calc
        Real.sqrt h * (Real.sqrt h * Real.sqrt r) =
            (Real.sqrt h * Real.sqrt h) * Real.sqrt r := by ring
        _ = h * Real.sqrt r := by rw [Real.mul_self_sqrt hh.le]
    _ = h / Real.sqrt (h * r) := by rw [Real.sqrt_mul hh.le]

theorem net_two_identity (d n N : Real) (hd : 0 <= d) (hn : 0 <= n) :
    net d n N 2 =
      (c ^ 2 * N - 4 * c) * (d + 2) /
        (16 * Real.sqrt ((d + 2) * (n + 1))) - 1 / 2 := by
  have hd2 : 0 < d + 2 := by linarith
  have hn1 : 0 < n + 1 := by linarith
  have ht : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  have ht2 : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrecip : 1 / Real.sqrt (2 : Real) = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt ht)).2
    nlinarith only [ht2]
  have hbracket :
      (c * N / 8 - 1) * Real.sqrt 2 + 1 / Real.sqrt 2 =
        (c * N / 8 - 1 / 2) * Real.sqrt 2 := by
    rw [hrecip]
    ring
  have hrad := radical_identity (d + 2) (n + 1) hd2 hn1
  unfold net
  rw [hbracket]
  calc
    c / 2 * Real.sqrt ((d + 2) / (2 * (n + 1))) *
        ((c * N / 8 - 1 / 2) * Real.sqrt 2) - 1 / 2 =
        c / 2 * (c * N / 8 - 1 / 2) *
          (Real.sqrt ((d + 2) / (2 * (n + 1))) * Real.sqrt 2) - 1 / 2 := by ring
    _ = c / 2 * (c * N / 8 - 1 / 2) *
        ((d + 2) / Real.sqrt ((d + 2) * (n + 1))) - 1 / 2 := by rw [hrad]
    _ = (c ^ 2 * N - 4 * c) * (d + 2) /
        (16 * Real.sqrt ((d + 2) * (n + 1))) - 1 / 2 := by ring

theorem net_mono_k (d n N k : Real) (hN : 30 <= N) (hk : 2 <= k) :
    net d n N 2 <= net d n N k := by
  have hB : 1 <= c * N / 8 - 1 := by
    dsimp [c]
    linarith
  have ha : 0 <= c / 2 * Real.sqrt ((d + 2) / (2 * (n + 1))) := by
    unfold c
    positivity
  have hcompare := sqrt_weighted_reciprocal_le (c * N / 8 - 1) k hB hk
  have hscaled := mul_le_mul_of_nonneg_left hcompare ha
  unfold net
  linarith only [hscaled]

theorem lowerBound_le_net (d n N k : Real)
    (hd : 0 <= d) (hn : 0 <= n) (hk : 2 <= k) (hN : 30 <= N)
    (hfloor : (n - 2 * d - 14) / (d + 2) <= N) :
    lowerBound d n <= net d n N k := by
  have hd2 : 0 < d + 2 := by linarith
  have hfloorMul : n - 2 * d - 14 <= N * (d + 2) :=
    (div_le_iff₀ hd2).1 hfloor
  have hscaled := mul_le_mul_of_nonneg_left hfloorMul (sq_nonneg c)
  have hnum :
      c ^ 2 * (n - 2 * d - 14) - 4 * c * (d + 2) <=
        (c ^ 2 * N - 4 * c) * (d + 2) := by
    nlinarith only [hscaled]
  have hden : 0 <= 16 * Real.sqrt ((d + 2) * (n + 1)) := by positivity
  have hquot := div_le_div_of_nonneg_right hnum hden
  calc
    lowerBound d n <=
        (c ^ 2 * N - 4 * c) * (d + 2) /
          (16 * Real.sqrt ((d + 2) * (n + 1))) - 1 / 2 := by
      unfold lowerBound
      linarith only [hquot]
    _ = net d n N 2 := (net_two_identity d n N hd hn).symm
    _ <= net d n N k := net_mono_k d n N k hN hk

end BanditRhoOneBridge

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-rho-one-bridge-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-rho-one-normalization-v1.lean" SHA256 4a69e164a266b55d367cbeb789cb5dda52f279280a310a2669a5ff20c1bb2e04

set_option autoImplicit false

noncomputable section

namespace BanditRhoOneNormalization

theorem net_identity (d n N k : Real)
    (hd : 0 <= d) (hn : 0 < n) (hk : 2 <= k) :
    BanditUnsaturated.net 1 k N (BanditUnsaturated.deltaMax 1 n k d) =
      BanditRhoOneBridge.net d n N k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 < k := by linarith only [hk]
  have hn1 : 0 < n + 1 := by linarith only [hn]
  have hkroot : Not (Real.sqrt k = 0) := ne_of_gt (Real.sqrt_pos.2 hk0)
  let H : Real := Real.sqrt ((d + 2) / (2 * (n + 1)))
  have hbase : 0 <= (d + 2) / (2 * (n + 1)) := by positivity
  have hratio :
      (1 + d + 1) / (2 * k * (n + 1)) =
        ((d + 2) / (2 * (n + 1))) / k := by
    rw [div_div]
    congr 1 <;> ring
  have hsmallRoot :
      Real.sqrt ((1 + d + 1) / (2 * k * (n + 1))) = H / Real.sqrt k := by
    rw [hratio, Real.sqrt_div hbase]
  have hcancel : k / Real.sqrt k = Real.sqrt k := by
    apply (div_eq_iff hkroot).2
    exact (Real.mul_self_sqrt hk0.le).symm
  have hbigRoot :
      Real.sqrt ((1 + d + 1) * k / (2 * (n + 1))) = H * Real.sqrt k := by
    calc
      _ = k * Real.sqrt ((1 + d + 1) / (2 * k * (n + 1))) :=
        BanditUnsaturated.root_identity 1 n k d (by norm_num) hn hk0 hd
      _ = k * (H / Real.sqrt k) := by rw [hsmallRoot]
      _ = H * (k / Real.sqrt k) := by ring
      _ = H * Real.sqrt k := by rw [hcancel]
  have hdelta :
      BanditUnsaturated.deltaMax 1 n k d =
        BanditUnsaturated.c / 2 * H * (Real.sqrt k - 1 / Real.sqrt k) := by
    unfold BanditUnsaturated.deltaMax
    rw [hsmallRoot]
    calc
      BanditUnsaturated.c * (k - 1) / 2 * (H / Real.sqrt k) =
          BanditUnsaturated.c / 2 * H * ((k - 1) / Real.sqrt k) := by ring
      _ = BanditUnsaturated.c / 2 * H * (Real.sqrt k - 1 / Real.sqrt k) := by
        rw [sub_div, hcancel]
  have hgain :
      BanditUnsaturated.gain 1 n k N d =
        BanditUnsaturated.c ^ 2 * N / 16 * H * Real.sqrt k := by
    unfold BanditUnsaturated.gain
    rw [hbigRoot]
    ring
  rw [BanditUnsaturated.net_at_max 1 n k N d (by norm_num) hn hk1 hd,
    hgain, hdelta]
  change BanditUnsaturated.c ^ 2 * N / 16 * H * Real.sqrt k -
      1 * (1 / 2 + BanditUnsaturated.c / 2 * H *
        (Real.sqrt k - 1 / Real.sqrt k)) =
    BanditUnsaturated.c / 2 * H *
      ((BanditUnsaturated.c * N / 8 - 1) * Real.sqrt k + 1 / Real.sqrt k) - 1 / 2
  ring

end BanditRhoOneNormalization

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-rho-one-normalization-v1.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-total-rate-v3.lean" SHA256 6e58c00e6a61bc1f13bef6967a8c43132802d7ba09ec3689b448a49a53eefe4b

set_option autoImplicit false

noncomputable section

namespace BanditTotalRate

theorem rho_one_coefficient (d : Nat) (n : Real)
    (hd : d <= 3) (hn : 240 <= n) (hmax : n <= 3000)
    (h320 : 1 <= d -> 320 <= n) (h400 : 2 <= d -> 400 <= n)
    (h840 : 3 <= d -> 840 <= n) :
    n / 12500 <= BanditRhoOneBridge.lowerBound (d : Real) n := by
  interval_cases d
  · simpa only [Nat.cast_zero, BanditSmallRho.lowerBound, BanditRhoOneBridge.lowerBound,
      BanditSmallRho.c, BanditRhoOneBridge.c] using BanditSmallRho.rho_one_depth_zero n hn hmax
  · simpa only [Nat.cast_one, BanditSmallRho.lowerBound, BanditRhoOneBridge.lowerBound,
      BanditSmallRho.c, BanditRhoOneBridge.c] using BanditSmallRho.rho_one_depth_one n (h320 (by omega)) hmax
  · exact BanditSmallRho.rho_one_depth_two n (h400 (by omega)) hmax
  · exact BanditSmallRho.rho_one_depth_three n (h840 (by omega)) hmax

theorem rate (S A n d k rho N : Nat) (D : Real)
    (f : BanditConstruction.Facts S A n d k rho N D)
    (hbudgetOriginal : D * (S : Real) * (A : Real) <= (n : Real)) :
    (1 / 12500 : Real) * Real.sqrt (D * (S : Real) * (A : Real) * (n : Real)) <=
      BanditUnsaturated.net (rho : Real) (k : Real) (N : Real)
        (BanditWitnessAssembly.chosenDelta n d k (rho : Real)) := by
  have hrho : 0 < (rho : Real) := by exact_mod_cast (show 0 < rho from lt_of_lt_of_le (by decide) f.rho_pos)
  have hn240 : (240 : Real) <= (n : Real) := by exact_mod_cast f.horizon_ge_240
  have hn : 0 < (n : Real) := by linarith only [hn240]
  have hk : (2 : Real) <= (k : Real) := by exact_mod_cast f.family_ge_two
  have hN : (30 : Real) <= (N : Real) := by exact_mod_cast f.N_ge_thirty
  have hd : 0 <= (d : Real) := Nat.cast_nonneg d
  have hD : 0 <= D := by linarith only [f.diameter_gt_twenty]
  have hs : 0 <= ((S * A : Nat) : Real) := Nat.cast_nonneg (S * A)
  have hbudget : D * ((S * A : Nat) : Real) <= (n : Real) := by
    simpa only [Nat.cast_mul, mul_assoc] using hbudgetOriginal
  have h100 : 100 * (rho : Real) <= (n : Real) := by exact_mod_cast f.horizon
  have hhorizon : (rho : Real) <= (n : Real) / 100 := by linarith only [h100]
  have hsize : ((S * A : Nat) : Real) <= 6 * (k : Real) := by
    exact_mod_cast f.size_le_six_family
  have htargetIdentity :
      (1 / 12500 : Real) * Real.sqrt (D * (S : Real) * (A : Real) * (n : Real)) =
        Real.sqrt (D * ((S * A : Nat) : Real) * (n : Real)) / 12500 := by
    rw [Nat.cast_mul]
    ring_nf
  rw [htargetIdentity]
  unfold BanditWitnessAssembly.chosenDelta
  by_cases hsat : (1 / 4 : Real) <=
      BanditUnsaturated.deltaMax (rho : Real) (n : Real) (k : Real) (d : Real)
  · rw [min_eq_left hsat]
    have hdepth : (d : Real) <= 3 * (rho : Real) := by exact_mod_cast f.depth_le_three
    exact BanditRateBranches.saturated (rho : Real) (n : Real) (k : Real) (N : Real)
      (d : Real) D ((S * A : Nat) : Real) hrho hn.le hk hN hd hD hs hbudget hdepth hhorizon f.N_floor
  · have hDelta : BanditUnsaturated.deltaMax (rho : Real) (n : Real) (k : Real) (d : Real) <= 1 / 4 :=
      (lt_of_not_ge hsat).le
    rw [min_eq_right hDelta]
    by_cases hone : rho = 1
    · subst rho
      have hmax : (n : Real) <= 3000 := by
        exact_mod_cast (f.rho_one_horizon rfl).le
      have h320 : 1 <= d -> (320 : Real) <= (n : Real) := by
        intro hd1
        exact_mod_cast f.horizon_ge_320 hd1
      have h400 : 2 <= d -> (400 : Real) <= (n : Real) := by
        intro hd2
        exact_mod_cast f.horizon_ge_400 hd2
      have h840 : 3 <= d -> (840 : Real) <= (n : Real) := by
        intro hd3
        exact_mod_cast f.horizon_ge_840 hd3
      have hcoeff := rho_one_coefficient d (n : Real) (f.depth_le_three_of_one rfl)
        hn240 hmax h320 h400 h840
      have hfloor : ((n : Real) - 2 * (d : Real) - 14) / ((d : Real) + 2) <= (N : Real) := by
        simpa only [Nat.cast_one, mul_one, add_comm] using f.N_floor
      have hbridge := BanditRhoOneBridge.lowerBound_le_net (d : Real) (n : Real) (N : Real) (k : Real)
        hd hn.le hk hN hfloor
      have htarget : Real.sqrt (D * ((S * A : Nat) : Real) * (n : Real)) / 12500 <= (n : Real) / 12500 :=
        BanditFiniteNet.target_le_horizon D ((S * A : Nat) : Real) (n : Real) hD hs hn.le hbudget
      simpa only [Nat.cast_one, BanditRhoOneNormalization.net_identity (d : Real) (n : Real) (N : Real) (k : Real) hd hn hk]
        using htarget.trans (hcoeff.trans hbridge)
    · have htwo : 2 <= rho := by have := f.rho_pos; omega
      by_cases hlarge : 5 <= rho
      · have hdepth : (d : Real) <= (rho : Real) := by exact_mod_cast f.depth_le_of_five hlarge
        have hkn : 4800 * (rho : Real) <= (k : Real) * (n : Real) := by
          exact_mod_cast f.product_lower_of_five hlarge
        exact BanditRateBranches.large (rho : Real) (n : Real) (k : Real) (N : Real)
          (d : Real) D ((S * A : Nat) : Real) hrho hn hk hN hd hD hs hdepth hhorizon f.N_floor hkn f.size_rate_bound
      · have hrho4 : rho <= 4 := by omega
        have h120 : 120 * (d : Real) <= (n : Real) := by exact_mod_cast f.depth_horizon.le
        have hkn : 3000 * (rho : Real) <= (k : Real) * (n : Real) := by
          exact_mod_cast f.product_lower_of_two htwo
        exact BanditRateBranches.finite rho d (n : Real) (k : Real) (N : Real) D ((S * A : Nat) : Real)
          htwo hrho4 (f.depth_le_four hrho4) hk hN hD hs hbudget h100 h120 f.N_floor hkn hsize
          (f.active_real_cap htwo) hDelta

end BanditTotalRate

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-total-rate-v3.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-tail-v3.lean" SHA256 76a538136e5473cb5d89fcd19777d519048be895ec1e6d9215e5583553e40940

set_option autoImplicit false

noncomputable section

namespace BanditParameterTail

def base (rho : Nat) : Real := 1 + 1 / (2 * (rho : Real))

theorem base_ge_one (rho : Nat) : 1 <= base rho := by
  unfold base
  have h : (0 : Real) <= 1 / (2 * (rho : Real)) := by positivity
  linarith

theorem reciprocal_bounds (rho : Nat) (h : 1 <= rho) :
    0 < 1 / (rho : Real) ∧ 1 / (rho : Real) <= 1 := by
  have hr : (1 : Real) <= rho := by exact_mod_cast h
  constructor
  · positivity
  · exact (div_le_one (by positivity)).2 hr

theorem block_short (rho : Nat) (h : 1 <= rho) :
    2 <= (1 + 1 / (rho : Real)) * base rho ^ (2 * rho - 2) := by
  have hr : (0 : Real) < rho := by exact_mod_cast (show 0 < rho by omega)
  have he : ((2 * rho - 2 : Nat) : Real) = 2 * (rho : Real) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  have hb := one_add_mul_le_pow
    (show (-2 : Real) <= 1 / (2 * (rho : Real)) by
      have hp : (0 : Real) <= 1 / (2 * (rho : Real)) := by positivity
      linarith) (2 * rho - 2)
  have heq : (1 : Real) + (2 * (rho : Real) - 2) * (1 / (2 * (rho : Real))) =
      2 - 1 / (rho : Real) := by
    field_simp
    ring
  rw [he, heq] at hb
  change 2 - 1 / (rho : Real) <= base rho ^ (2 * rho - 2) at hb
  obtain ⟨ha0, ha1⟩ := reciprocal_bounds rho h
  have hmul := mul_le_mul_of_nonneg_left hb (show 0 <= 1 + 1 / (rho : Real) by positivity)
  have hsq := mul_le_mul_of_nonneg_left ha1 ha0.le
  nlinarith

theorem block_long (rho : Nat) (h : 1 <= rho) :
    64 <= base rho ^ (12 * rho) := by
  have hr : (0 : Real) < rho := by exact_mod_cast (show 0 < rho by omega)
  have hb := one_add_mul_le_pow
    (show (-2 : Real) <= 1 / (2 * (rho : Real)) by
      have hp : (0 : Real) <= 1 / (2 * (rho : Real)) := by positivity
      linarith) (2 * rho)
  have heq : (1 : Real) + ((2 * rho : Nat) : Real) * (1 / (2 * (rho : Real))) = 2 := by
    push_cast
    field_simp
    ring
  rw [heq] at hb
  change (2 : Real) <= base rho ^ (2 * rho) at hb
  calc
    (64 : Real) = (2 : Real) ^ 6 := by norm_num
    _ <= (base rho ^ (2 * rho)) ^ 6 := pow_le_pow_left₀ (by norm_num) hb 6
    _ = base rho ^ (12 * rho) := by
      rw [← pow_mul]
      congr 1
      omega

theorem tail_bound (rho N R : Nat) (h : 1 <= rho)
    (hR : (2 * rho - 2) * N + 12 * rho <= R) :
    (2 : Real) ^ N <= (1 / 64 : Real) * (1 + 1 / (rho : Real)) ^ N * base rho ^ R := by
  have ht1 := base_ge_one rho
  have ht0 : 0 <= base rho := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : Real) <= 2) (block_short rho h) N
  rw [mul_pow, ← pow_mul] at hp
  have hlarge : base rho ^ ((2 * rho - 2) * N) * 64 <= base rho ^ R := by
    calc
      _ <= base rho ^ ((2 * rho - 2) * N) * base rho ^ (12 * rho) :=
        mul_le_mul_of_nonneg_left (block_long rho h) (pow_nonneg ht0 _)
      _ = base rho ^ ((2 * rho - 2) * N + 12 * rho) := (pow_add _ _ _).symm
      _ <= base rho ^ R := pow_le_pow_right₀ ht1 hR
  calc
    (2 : Real) ^ N <= (1 + 1 / (rho : Real)) ^ N * base rho ^ ((2 * rho - 2) * N) := hp
    _ = (1 / 64 : Real) * (1 + 1 / (rho : Real)) ^ N *
        (base rho ^ ((2 * rho - 2) * N) * 64) := by ring
    _ <= (1 / 64 : Real) * (1 + 1 / (rho : Real)) ^ N * base rho ^ R :=
      mul_le_mul_of_nonneg_left hlarge (by positivity)

end BanditParameterTail

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-hatcher-root-bandit-tail-v3.lean"

-- BEGIN "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-final-proof-v1.lean" SHA256 e8902065fba40efad4fd82b883421cfc34516b85e60d9cfd62f89b97b397c16d

set_option autoImplicit false

open scoped NNReal

theorem BanditAlgorithm.arena_lower_bound_parameter_choice
    (S A n L d k : ℕ) (D : ℝ)
    (hS : 3 ≤ S) (hA : 2 ≤ A)
    (hD : 20 * (1 + Real.log S / Real.log A) ≤ D)
    (hn : D * S * A ≤ (n : ℝ))
    (hdep : A ^ d < A * (S - 2)) (hL : S - 2 ≤ 3 * L + 1) (hL1 : 1 ≤ L)
    (hk : k = L * A) :
    ∃ (δ Δ : ℝ≥0) (N : ℕ) (ε c₁ c₂ c₃ Dsc : ℝ),
      δ ≤ 1 ∧ (0 : ℝ) < δ ∧ Δ ≤ 1 / 4 ∧ Δ ≤ 1 / 2 ∧
      2 ≤ k ∧ 0 < n ∧ 0 < N ∧ 0 < Dsc ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      (N : ℝ) ≤ n / Dsc ∧ c₃ * Dsc ≤ 1 / (δ : ℝ) ∧
      c₁ * n / Dsc ≤ (1 - ε) * N ∧
      ((n : ℝ) + 1 / (δ : ℝ)) / (1 / (δ : ℝ) + d + 1) ≤ c₂ * n / Dsc ∧
      d + N * (d + 2) ≤ n ∧
      (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N * (1 + (δ : ℝ) / 2) ^ (n - d - N * (d + 2)) ∧
      (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (Dsc / (2 * c₂ * n * k)) ∧
      4 * (1 / (δ : ℝ) + d + 1) ≤ D ∧
      (1 / 12500) * Real.sqrt (D * S * A * n)
        ≤ c₁ ^ 2 * c₃ / 16 * Real.sqrt (Dsc * k * n / (2 * c₂))
            - (1 / 2 + (Δ : ℝ)) / (δ : ℝ) := by
  let rho : Nat := BanditCaps.rho D d k n
  let count : Nat := BanditTruncation.N n d rho
  have f : BanditConstruction.Facts S A n d k rho count D :=
    BanditConstruction.constructFacts S A n L d k D hS hA hD hn hdep hL hL1 hk
  have hnPos : 0 < n :=
    lt_of_lt_of_le (by decide : 0 < 240) f.horizon_ge_240
  have hrho : (1 : Real) <= (rho : Real) := by exact_mod_cast f.rho_pos
  have hbudget : d + count * (d + 2) <= n :=
    BanditTruncation.allocation_le f.rho_pos f.horizon f.depth_horizon
  have hrem : (2 * rho - 2) * count + 12 * rho <= n - d - count * (d + 2) :=
    BanditTruncation.remainder_lower f.rho_pos f.horizon f.depth_horizon
  have htailRaw := BanditParameterTail.tail_bound rho count
    (n - d - count * (d + 2)) f.rho_pos hrem
  have hbase : BanditParameterTail.base rho = 1 + (1 / (rho : Real)) / 2 := by
    unfold BanditParameterTail.base
    rw [div_div, mul_comm (rho : Real) 2]
  have htail : (2 : Real) ^ count <=
      (1 / 64) * (1 + 1 / (rho : Real)) ^ count *
        (1 + (1 / (rho : Real)) / 2) ^ (n - d - count * (d + 2)) := by
    simpa only [hbase] using htailRaw
  exact BanditWitnessAssembly.exists_parameters_of_net_rate S A n d k count
    (rho : Real) D hrho f.N_ge_thirty f.family_ge_two hnPos hbudget htail f.diameter
    (BanditTotalRate.rate S A n d k rho count D f hn)

theorem solution
    (S A n L d k : ℕ) (D : ℝ)
    (hS : 3 ≤ S) (hA : 2 ≤ A)
    (hD : 20 * (1 + Real.log S / Real.log A) ≤ D)
    (hn : D * S * A ≤ (n : ℝ))
    (hdep : A ^ d < A * (S - 2)) (hL : S - 2 ≤ 3 * L + 1) (hL1 : 1 ≤ L)
    (hk : k = L * A) :
    ∃ (δ Δ : ℝ≥0) (N : ℕ) (ε c₁ c₂ c₃ Dsc : ℝ),
      δ ≤ 1 ∧ (0 : ℝ) < δ ∧ Δ ≤ 1 / 4 ∧ Δ ≤ 1 / 2 ∧
      2 ≤ k ∧ 0 < n ∧ 0 < N ∧ 0 < Dsc ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      (N : ℝ) ≤ n / Dsc ∧ c₃ * Dsc ≤ 1 / (δ : ℝ) ∧
      c₁ * n / Dsc ≤ (1 - ε) * N ∧
      ((n : ℝ) + 1 / (δ : ℝ)) / (1 / (δ : ℝ) + d + 1) ≤ c₂ * n / Dsc ∧
      d + N * (d + 2) ≤ n ∧
      (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N * (1 + (δ : ℝ) / 2) ^ (n - d - N * (d + 2)) ∧
      (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (Dsc / (2 * c₂ * n * k)) ∧
      4 * (1 / (δ : ℝ) + d + 1) ≤ D ∧
      (1 / 12500) * Real.sqrt (D * S * A * n)
        ≤ c₁ ^ 2 * c₃ / 16 * Real.sqrt (Dsc * k * n / (2 * c₂))
            - (1 / 2 + (Δ : ℝ)) / (δ : ℝ) := by
  exact BanditAlgorithm.arena_lower_bound_parameter_choice S A n L d k D hS hA hD hn hdep hL hL1 hk

-- END "/Users/ryanshin/conductor/workspaces/prove2me-farming-results/papeete/.context/continuous-legacy-static-bandit-final-proof-v1.lean"
