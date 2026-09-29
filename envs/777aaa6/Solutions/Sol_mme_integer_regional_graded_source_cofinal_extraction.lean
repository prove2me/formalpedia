-- Prove2me | solution 1 for mme_integer_regional_graded_source_cofinal_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-20T19:16:30.021985+00:00
-- url     : https://prove2.me/submissions/907c377c-ff10-4a9a-aede-c291cf407a61

import Theorems.Thm_mme_integer_regional_step_subexponential_repair
import Theorems.Thm_mme_integer_regional_entropy_copy_bound
import Theorems.Thm_mme_recursive_region_exact_step_realization_of_graded_source
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Mathlib

open BigOperators MME MME.RegionRate MME.RegionRealization MME.ProfiledCW
open MME.RecursiveYZ
open scoped Classical
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem round_div_lower {x y : ℝ} {r : ℕ} (hr : 0 < r)
    (hy : 1 ≤ y) (hx : 2 * (r : ℝ) * y ≤ x) :
    y ≤ (⌊x⌋₊ / r : ℕ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : ⌊x⌋₊ / r = ⌊x / (r : ℝ)⌋₊ := by
    simpa only [div_mul_cancel₀ _ (ne_of_gt hr')] using
      Nat.mul_cast_floor_div_cancel (ne_of_gt hr) (x / (r : ℝ))
  rw [heq]
  have hh : 2 * y ≤ x / (r : ℝ) := (le_div_iff₀ hr').2 (by nlinarith)
  have hf := Nat.sub_one_lt_floor (x / (r : ℝ))
  linarith

private theorem polynomial_log_bound {A k x : ℝ} {d : ℕ}
    (hA : 1 ≤ A) (hk : 1 ≤ k) (hx : 0 < x)
    (hpoly : x ≤ A * (k + 1) ^ d) :
    Real.log x ≤ (Real.log A + d) * k := by
  have ha : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hk' : 0 < k + 1 := by linarith
  have hh := Real.log_le_log hx hpoly
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (pow_pos hk' d)), Real.log_pow] at hh
  have hl : Real.log (k + 1) ≤ k := by
    simpa using Real.log_le_sub_one_of_pos hk'
  have hla : 0 ≤ Real.log A := Real.log_nonneg hA
  have hd : 0 ≤ (d : ℝ) := by positivity
  nlinarith [mul_nonneg hla (sub_nonneg.mpr hk), mul_nonneg hd (sub_nonneg.mpr hl)]

private theorem entropy_lower_linear_loss {A B E k s theta F P : ℝ} {d : ℕ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hk : 1 ≤ k)
    (hF : 0 < F) (hP : 0 < P)
    (hFp : F ≤ A * (k + 1) ^ d) (hPp : P ≤ A * (k + 1) ^ d)
    (hs : E * k ^ 2 ≤ s) (ht : theta ≤ B * k ^ 2) :
    Real.exp (E * k ^ 2 -
      (4 * Real.sqrt (Real.log A + d + B) + Real.log 32 + 2 * (Real.log A + d)) * k) ≤
      Real.exp (s - 4 * Real.sqrt (Real.log F + theta)) / (32 * P * F) := by
  have hf := polynomial_log_bound hA hk hF hFp
  have hp := polynomial_log_bound hA hk hP hPp
  have hk0 : 0 ≤ k := by linarith
  have hl : 0 ≤ Real.log A + d := add_nonneg (Real.log_nonneg hA) (Nat.cast_nonneg _)
  have hquad : (Real.log A + d) * k ≤ (Real.log A + d) * k ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hl
    nlinarith
  have ht' : Real.log F + theta ≤ (Real.log A + d + B) * k ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (Real.log F + theta) ≤ Real.sqrt (Real.log A + d + B) * k := by
    calc
      _ ≤ Real.sqrt ((Real.log A + d + B) * k ^ 2) := Real.sqrt_le_sqrt ht'
      _ = _ := by rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hk0]
  have hd : 0 < 32 * P * F := by positivity
  have hlog : Real.log (32 * P * F) ≤ (Real.log 32 + 2 * (Real.log A + d)) * k := by
    rw [Real.log_mul (by positivity) (ne_of_gt hF), Real.log_mul (by norm_num) (ne_of_gt hP)]
    have h32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg h32 (sub_nonneg.mpr hk)]
  rw [← Real.exp_log hd, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith


private theorem cofinal_count (C d : ℕ) (A B E rho : ℝ)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ {ell M : ℕ} {P : Predicate M}
      (D : IntegerStep ell M P), D.repairScale = k → M ≤ C * k ^ 2 →
      scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell ≤
        A * ((k : ℝ) + 1) ^ d →
      polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) ≤
        A * ((k : ℝ) + 1) ^ d →
      E * (k : ℝ) ^ 2 ≤ regionalRate D.total D.n D.m D.mu -
        ((∑ r, D.n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon →
      scaleExponent D.total D.n D.m D.mu D.epsilon ≤ B * (k : ℝ) ^ 2 →
      Real.exp (rho * (k : ℝ) ^ 2) ≤ (D.entropyCopies : ℝ) := by
  let delta : ℝ := (E - rho) / 4
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let loss : ℝ := 4 * Real.sqrt (Real.log A + d + B) + Real.log 32 + 2 * (Real.log A + d)
  obtain ⟨kR,hkR⟩ := mme_integer_regional_step_subexponential_repair C delta hdelta
  obtain ⟨kL,hkL⟩ := exists_nat_gt (max 1 (max (loss / delta) (Real.log 2 / delta)))
  refine ⟨max kR kL, ?_⟩
  intro k hk ell M P D hrepair hsize hF hP hE htheta
  have hkR' : kR ≤ k := (le_max_left _ _).trans hk
  have hkL' : (kL : ℝ) ≤ k := by exact_mod_cast (le_max_right kR kL).trans hk
  have hklarge : max 1 (max (loss / delta) (Real.log 2 / delta)) < (k : ℝ) := hkL.trans_le hkL'
  have hk1 : (1 : ℝ) ≤ k := (le_max_left _ _).trans hklarge.le
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hLoss : loss ≤ delta * (k : ℝ) := by
    have hh : loss / delta ≤ (k : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hklarge.le)
    exact (div_le_iff₀ hdelta).mp hh |>.trans_eq (mul_comm _ _)
  have hTwo : Real.log 2 ≤ delta * (k : ℝ) ^ 2 := by
    have hh : Real.log 2 / delta ≤ (k : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hklarge.le)
    have hh' := (div_le_iff₀ hdelta).mp hh
    have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hdelta.le (sub_nonneg.mpr hkk)]
  have hrepair' := hkR k hkR' D hrepair hsize
  have hFpos : 0 < scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell := by
    unfold scaleFactor loadFactor polynomialFactor ambientFactor
    positivity
  have hPpos : 0 < polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) := by
    unfold polynomialFactor
    positivity
  have hlinear := entropy_lower_linear_loss hA hB hk1 hFpos hPpos hF hP hE htheta
  have hlower : Real.exp ((E - delta) * (k : ℝ) ^ 2) ≤ D.entropyLower := by
    apply le_trans _ hlinear
    apply Real.exp_le_exp.mpr
    change (E - delta) * (k : ℝ) ^ 2 ≤ E * (k : ℝ) ^ 2 - loss * k
    nlinarith [mul_nonneg (sub_nonneg.mpr hLoss) hk0]
  have hp8 : 0 < 8 ^ D.repairExponent := by positivity
  have hp8r : (0 : ℝ) < (8 ^ D.repairExponent : ℕ) := by exact_mod_cast hp8
  have hrepair'' : Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) < delta * (k : ℝ) ^ 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hrepair'
  have hround : 2 * ((8 ^ D.repairExponent : ℕ) : ℝ) * Real.exp (rho * (k : ℝ) ^ 2) ≤ D.entropyLower := by
    apply le_trans _ hlower
    calc
      _ = Real.exp (Real.log 2 + Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) + rho * (k : ℝ) ^ 2) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hp8r]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hgap' : E - rho = 4 * delta := by dsimp [delta]; ring
        nlinarith
  exact round_div_lower hp8 (Real.one_le_exp (mul_nonneg hrho (sq_nonneg _))) hround

private theorem overhead_bounds {half R ell C H d k : ℕ}
    {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (hk : 1 ≤ k) (hs : (∑ r, n r) ≤ C * k ^ 2) (hh : half ≤ H)
    (hc : Fintype.card (RecursiveYZ.Cell half R parent) ≤ d)
    (hj : R * (half + 1) ≤ d)
    (hw : R * (half + 1) * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell) ≤ d) :
    let A : ℝ := (H + 138) * (6 * (C + 1)) ^ (2 * d)
    scaleFactor (half := half) (parent := parent) n k ell ≤ A * ((k : ℝ) + 1) ^ (4 * d + 1) ∧
    polynomialFactor n (Fintype.card (RecursiveYZ.Cell half R parent)) ≤ A * ((k : ℝ) + 1) ^ (4 * d + 1) := by
  let b : ℝ := 6 * (C + 1)
  let v : ℝ := (k : ℝ) + 1
  let T : ℝ := (b * v ^ 2) ^ d
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hv : 1 ≤ v := by dsimp [v]; linarith
  have hb : 1 ≤ b := by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) C; linarith
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hbv : 1 ≤ b * v ^ 2 := one_le_mul_of_one_le_of_one_le hb hv2
  have hT : 1 ≤ T := one_le_pow₀ hbv
  have hs' : ((∑ r, n r : ℕ) : ℝ) ≤ (C : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hs
  have hbase : 6 * (((∑ r, n r : ℕ) : ℝ) + 1) ≤ b * v ^ 2 := by
    dsimp [b, v]
    have hC : (0 : ℝ) ≤ C := by positivity
    nlinarith [mul_nonneg hC hk0]
  have hp : ∀ j : ℕ, j ≤ d → polynomialFactor n j ≤ T := by
    intro j hj'
    unfold polynomialFactor
    exact (pow_le_pow_left₀ (by positivity) hbase j).trans (pow_le_pow_right₀ hbv hj')
  have hpc := hp _ hc
  have hpj := hp _ hj
  have hpw := hp _ hw
  have ham : ambientFactor (half := half) (parent := parent) n ≤ T := by
    apply le_trans _ hpc
    unfold ambientFactor polynomialFactor
    apply pow_le_pow_left₀ (by positivity)
    have hn : (0 : ℝ) ≤ ((∑ r, n r : ℕ) : ℝ) := by positivity
    linarith
  have hpos : ∀ j : ℕ, 0 ≤ polynomialFactor n j := by intro j; unfold polynomialFactor; positivity
  have ha0 : 0 ≤ ambientFactor (half := half) (parent := parent) n := by unfold ambientFactor; positivity
  have hscale : scaleFactor (half := half) (parent := parent) n k ell ≤
      (H + 138) * v * T ^ 2 := by
    have hab : ambientFactor (half := half) (parent := parent) n * polynomialFactor n (R * (half + 1)) ≤ T * T :=
      mul_le_mul ham hpj (hpos _) (by linarith)
    have hpw' : polynomialFactor n (R * (half + 1)) *
        polynomialFactor n (R * (half + 1) * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell)) ≤ T * T :=
      mul_le_mul hpj hpw (hpos _) (by linarith)
    have hh' : (half : ℝ) ≤ H := by exact_mod_cast hh
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hvT : 1 ≤ v * T ^ 2 := one_le_mul_of_one_le_of_one_le hv hT2
    have hconst : (H : ℝ) + 2 ≤ (H + 2) * v * T ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ H + 2 by positivity) (sub_nonneg.mpr hvT)]
    have hmul := mul_le_mul_of_nonneg_left hpw' (show (0 : ℝ) ≤ 128 * k by positivity)
    unfold scaleFactor loadFactor
    dsimp [v] at hconst ⊢
    nlinarith
  have hpoly : polynomialFactor n (Fintype.card (RecursiveYZ.Cell half R parent)) ≤
      (H + 138) * v * T ^ 2 := by
    apply hpc.trans
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hvT : T ^ 2 ≤ v * T ^ 2 := le_mul_of_one_le_left (by positivity) hv
    have hbig : 1 ≤ (H : ℝ) + 138 := by have := Nat.cast_nonneg (α := ℝ) H; linarith
    have hlast : v * T ^ 2 ≤ (H + 138) * (v * T ^ 2) :=
      le_mul_of_one_le_left (by positivity) hbig
    exact hT2.trans (hvT.trans (by simpa only [mul_assoc] using hlast))
  have heq : (H + 138) * v * T ^ 2 =
      ((H + 138) * (6 * (C + 1)) ^ (2 * d) : ℝ) * ((k : ℝ) + 1) ^ (4 * d + 1) := by
    dsimp [T, b, v]
    rw [← pow_mul, mul_pow, ← pow_mul]
    rw [show d * 2 = 2 * d by omega, show 2 * (2 * d) = 4 * d by omega, pow_succ]
    ring
  exact ⟨heq ▸ hscale, heq ▸ hpoly⟩

private theorem total_regions_le_length {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) : (∑ r, D.n r) ≤ M := by
  have hcard : D.L = (∑ r, D.n r) * 2 := by
    simpa only [Position, Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod,
      ← Finset.sum_mul] using Fintype.card_congr D.positions
  have hlen : D.L ≤ M := (Nat.le_mul_of_pos_right D.L (show 0 < 2 ^ (ell - 1) by positivity)).trans_eq D.length
  omega

theorem solution (C H d : ℕ) (B E rho : ℝ)
    (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ {ell M : ℕ} {P Q : Predicate M}
      (D : IntegerStep ell M P), D.repairScale = k → M ≤ C * k ^ 2 → D.half ≤ H →
      Fintype.card (Cell D.half D.R D.parent) ≤ d →
      D.R * (D.half + 1) ≤ d →
      D.R * (D.half + 1) * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell) ≤ d →
      E * (k : ℝ) ^ 2 ≤ regionalRate D.total D.n D.m D.mu -
        ((∑ r, D.n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon →
      scaleExponent D.total D.n D.m D.mu D.epsilon ≤ B * (k : ℝ) ^ 2 →
      (∀ (i : Fin 3) (a : Address D.half D.R D.parent D.n),
        a ∈ RecursiveXHash.target D.m → ∀ f ∈ unbrokenWords D.total i a (D.mu i),
          Q i (ProfiledCW.flatten D.positions D.length f)) →
      ∃ S : ExactStep ell M Q,
        Real.exp (rho * (k : ℝ) ^ 2) ≤ (S.copies : ℝ) ∧ S.output = D.output ∧
        ∀ (K : Type u) [Field K], TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin S.copies ↦ tensor K D.output)) (tensor K Q) := by
  let A : ℝ := (H + 138) * (6 * (C + 1)) ^ (2 * d)
  have hA : 1 ≤ A := by
    have hh : 1 ≤ (H : ℝ) + 138 := by have := Nat.cast_nonneg (α := ℝ) H; linarith
    have hb : 1 ≤ (6 * (C + 1) : ℝ) := by have := Nat.cast_nonneg (α := ℝ) C; linarith
    exact one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hb)
  obtain ⟨k0,hk0⟩ := cofinal_count C (4 * d + 1) A B E rho hA hB hrho hgap
  refine ⟨max k0 1, ?_⟩
  intro k hk ell M P Q D hrepair hsize hhalf hc hj hw hE htheta hQ
  have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hpoly := overhead_bounds D.n hk1 ((total_regions_le_length D).trans hsize) hhalf hc hj hw
  have hcount := hk0 k ((le_max_left _ _).trans hk) D hrepair hsize
  have hcop : Real.exp (rho * (k : ℝ) ^ 2) ≤ (D.entropyCopies : ℝ) :=
    hcount (by simpa only [hrepair] using hpoly.1) hpoly.2 hE htheta
  obtain ⟨S,hcount',hexp,hout⟩ :=
    mme_recursive_region_exact_step_realization_of_graded_source D.parent D.n
      D.total D.half_eq D.m D.hashPositions D.positions D.length D.mu D.mass D.support D.boundary
      D.reference D.reference_target D.minimum D.repairScale D.minimum_pos D.repairScale_gt_one
      D.parent_size D.split_divisible D.epsilon D.epsilon_pos D.size_test Q hQ
  have hh : D.lower ≤ (S.count : ℝ) := hcount'
  have he : S.stage.repairExponent = D.repairExponent := hexp
  have hcopies : D.copies ≤ S.copies := by
    change ⌊D.lower⌋₊ / 8 ^ D.repairExponent ≤ S.count / 8 ^ S.stage.repairExponent
    rw [he]
    exact Nat.div_le_div_right (Nat.floor_le_of_le hh)
  have hnum : D.entropyCopies ≤ S.copies :=
    (mme_integer_regional_entropy_copy_bound D).2.trans hcopies
  refine ⟨S, hcop.trans (by exact_mod_cast hnum), hout, ?_⟩
  intro K inst
  simpa only [hout] using (mme_recursive_profiled_CW_exact_step (K := K) S)
