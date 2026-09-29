-- Prove2me | solution 1 for mme_global_CW_canonical_cofinal_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:27:51.39456+00:00
-- url     : https://prove2.me/submissions/b3f146d3-d5a8-4227-8a2e-6e659233e716

import Definitions.Def_mme_global_CW_entropy_data
import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_global_CW_canonical_subexponential_repair
import Theorems.Thm_mme_global_CW_certified_entropy_copy_bound
open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

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

private theorem overhead_bounds {ell M C H d k : ℕ} (D : CountedStage ell M)
    (hrepair : D.repairScale = k)
    (hk : 1 ≤ k) (hs : (∑ r, D.n r) ≤ C * k ^ 2) (hh : D.degree ≤ H)
    (hc : Fintype.card (RecursiveYZ.Cell D.degree D.R D.bounds) ≤ d)
    (hj : D.R * (D.degree + 1) ≤ d)
    (hw : D.R * (D.degree + 1) * Fintype.card (CompleteSplit.CompleteWord ell) ≤ d) :
    let A : ℝ := (H + 138) * (6 * (C + 1)) ^ (2 * d)
    D.entropyScaleFactor ≤ A * ((k : ℝ) + 1) ^ (4 * d + 1) ∧
    polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.degree D.R D.bounds)) ≤ A * ((k : ℝ) + 1) ^ (4 * d + 1) := by
  let b : ℝ := 6 * (C + 1)
  let v : ℝ := (k : ℝ) + 1
  let T : ℝ := (b * v ^ 2) ^ d
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hv : 1 ≤ v := by dsimp [v]; linarith
  have hb : 1 ≤ b := by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) C; linarith
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hbv : 1 ≤ b * v ^ 2 := one_le_mul_of_one_le_of_one_le hb hv2
  have hT : 1 ≤ T := one_le_pow₀ hbv
  have hs' : ((∑ r, D.n r : ℕ) : ℝ) ≤ (C : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hs
  have hbase : 6 * (((∑ r, D.n r : ℕ) : ℝ) + 1) ≤ b * v ^ 2 := by
    dsimp [b, v]
    have hC : (0 : ℝ) ≤ C := by positivity
    nlinarith [mul_nonneg hC hk0]
  have hp : ∀ j : ℕ, j ≤ d → polynomialFactor D.n j ≤ T := by
    intro j hj'
    unfold polynomialFactor
    exact (pow_le_pow_left₀ (by positivity) hbase j).trans (pow_le_pow_right₀ hbv hj')
  have hpc := hp _ hc
  have hpj := hp _ hj
  have hpw := hp _ hw
  have ham : ambientFactor (half := D.degree) (parent := D.bounds) D.n ≤ T := by
    apply le_trans _ hpc
    unfold ambientFactor polynomialFactor
    apply pow_le_pow_left₀ (by positivity)
    have hn : (0 : ℝ) ≤ ((∑ r, D.n r : ℕ) : ℝ) := by positivity
    linarith
  have hpos : ∀ j : ℕ, 0 ≤ polynomialFactor D.n j := by intro j; unfold polynomialFactor; positivity
  have ha0 : 0 ≤ ambientFactor (half := D.degree) (parent := D.bounds) D.n := by unfold ambientFactor; positivity
  have hscale : D.entropyScaleFactor ≤
      (H + 138) * v * T ^ 2 := by
    have hab : ambientFactor (half := D.degree) (parent := D.bounds) D.n * polynomialFactor D.n (D.R * (D.degree + 1)) ≤ T * T :=
      mul_le_mul ham hpj (hpos _) (by linarith)
    have hpw' : polynomialFactor D.n (D.R * (D.degree + 1)) *
        polynomialFactor D.n (D.R * (D.degree + 1) * Fintype.card (CompleteSplit.CompleteWord ell)) ≤ T * T :=
      mul_le_mul hpj hpw (hpos _) (by linarith)
    have hh' : (D.degree : ℝ) ≤ H := by exact_mod_cast hh
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hvT : 1 ≤ v * T ^ 2 := one_le_mul_of_one_le_of_one_le hv hT2
    have hconst : (H : ℝ) + 2 ≤ (H + 2) * v * T ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ H + 2 by positivity) (sub_nonneg.mpr hvT)]
    have hmul := mul_le_mul_of_nonneg_left hpw' (show (0 : ℝ) ≤ 128 * k by positivity)
    unfold CountedStage.entropyScaleFactor CountedStage.entropyLoadFactor
    rw [hrepair]
    dsimp [v] at hconst ⊢
    nlinarith
  have hpoly : polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.degree D.R D.bounds)) ≤
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

private theorem entropy_log_linear_loss {A B E k s theta F P : ℝ} {d : ℕ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hk : 1 ≤ k)
    (hF : 0 < F) (hP : 0 < P)
    (hFp : F ≤ A * (k + 1) ^ d) (hPp : P ≤ A * (k + 1) ^ d)
    (hs : E * k ^ 2 ≤ s) (ht : theta ≤ B * k ^ 2) :
    E * k ^ 2 -
      (4 * Real.sqrt (Real.log A + d + B) + Real.log 64 + 2 * (Real.log A + d)) * k ≤
      s - Real.log P - Real.log (64 * F) - 4 * Real.sqrt (Real.log F + theta) := by
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
  rw [Real.log_mul (by norm_num) (ne_of_gt hF)]
  have h64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg h64 (sub_nonneg.mpr hk)]

private theorem total_le_length {ell M : ℕ} (D : HistogramFrame ell M) :
    (∑ r, D.n r) ≤ M := by
  have hcard : D.L = ∑ r, D.n r := by
    simpa only [Place,Fintype.card_fin,Fintype.card_sigma] using Fintype.card_congr D.positions
  have hlen : D.L ≤ M :=
    (Nat.le_mul_of_pos_right D.L (show 0 < 2 ^ (ell-1) by positivity)).trans_eq D.length
  omega

theorem solution (C H d : ℕ) (B E rho : ℝ)
    (hB : 0 ≤ B) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 1 < k,
      ∀ {ell M : ℕ} (D : HistogramFrame ell M) (mu : D.AdmissibleProfile),
      M ≤ C * k ^ 2 → D.degree ≤ H →
      Fintype.card (Cell D.degree D.R D.bounds) ≤ d →
      D.R * (D.degree+1) ≤ d →
      D.R * (D.degree+1) * Fintype.card (CompleteSplit.CompleteWord ell) ≤ d →
      E * (k : ℝ) ^ 2 ≤ (D.stage mu k hk).entropyRate →
      (D.stage mu k hk).entropyExponent ≤ B * (k : ℝ) ^ 2 →
      rho * (k : ℝ) ^ 2 ≤ (D.stage mu k hk).certifiedLogCopies := by
  let A : ℝ := (H + 138) * (6 * (C+1)) ^ (2*d)
  have hA : 1 ≤ A := by
    have hh : 1 ≤ (H : ℝ) + 138 := by have := Nat.cast_nonneg (α := ℝ) H; linarith
    have hb : 1 ≤ (6 * (C+1) : ℝ) := by have := Nat.cast_nonneg (α := ℝ) C; linarith
    exact one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hb)
  let delta : ℝ := (E-rho)/3
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let loss : ℝ := 4 * Real.sqrt (Real.log A + (4*d+1) + B) +
    Real.log 64 + 2 * (Real.log A + (4*d+1))
  obtain ⟨kR,hkR⟩ := mme_global_CW_canonical_subexponential_repair C delta hdelta
  obtain ⟨kL,hkL⟩ := exists_nat_gt (max 1 (loss/delta))
  refine ⟨max kR kL,?_⟩
  intro k hk
  obtain ⟨hk1,hrepair⟩ := hkR k ((le_max_left _ _).trans hk)
  refine ⟨hk1,?_⟩
  intro ell M D mu hsize hdegree hc hj hw hE htheta
  have hkL' : (kL : ℝ) ≤ k := by exact_mod_cast (le_max_right kR kL).trans hk
  have hklarge : max 1 (loss/delta) < (k : ℝ) := hkL.trans_le hkL'
  have hkreal : (1 : ℝ) ≤ k := (le_max_left _ _).trans hklarge.le
  have hloss : loss ≤ delta * (k : ℝ) := by
    have hh : loss/delta ≤ (k : ℝ) := (le_max_right _ _).trans hklarge.le
    simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hh
  have hpoly := overhead_bounds (D.stage mu k hk1) rfl (Nat.le_of_lt hk1)
    ((total_le_length D).trans hsize) hdegree hc hj hw
  have hF : 0 < (D.stage mu k hk1).entropyScaleFactor := by
    unfold CountedStage.entropyScaleFactor CountedStage.entropyLoadFactor polynomialFactor ambientFactor
    positivity
  have hP : 0 < polynomialFactor D.n (Fintype.card (Cell D.degree D.R D.bounds)) := by
    unfold polynomialFactor
    positivity
  have hlinear := entropy_log_linear_loss hA hB hkreal hF hP hpoly.1 hpoly.2 hE htheta
  have hr := hrepair D mu hsize
  apply le_trans _ (mme_global_CW_certified_entropy_copy_bound (D.stage mu k hk1))
  unfold CountedStage.entropyLogCopies
  have hlin : E * (k : ℝ)^2 - loss * k ≤
      (D.stage mu k hk1).entropyRate -
        Real.log (polynomialFactor D.n (Fintype.card (Cell D.degree D.R D.bounds))) -
        Real.log (64 * (D.stage mu k hk1).entropyScaleFactor) -
        4 * Real.sqrt (Real.log (D.stage mu k hk1).entropyScaleFactor +
          (D.stage mu k hk1).entropyExponent) := by
    convert hlinear using 1 <;> push_cast <;> ring
  have hgap' : E-rho = 3*delta := by dsimp [delta]; ring
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hloss hk0
  change rho * (k : ℝ)^2 ≤ _
  dsimp only [HistogramFrame.stage] at hlin hr ⊢
  have hgap2 := congrArg (fun x : ℝ ↦ x * (k : ℝ)^2) hgap'
  have hbudget : rho*(k : ℝ)^2 ≤ E*(k : ℝ)^2 - loss*k - delta*(k : ℝ)^2 := by
    nlinarith only [hsmall,hgap2,mul_nonneg hdelta.le (sq_nonneg (k : ℝ))]
  exact hbudget.trans (sub_le_sub hlin hr.le)
