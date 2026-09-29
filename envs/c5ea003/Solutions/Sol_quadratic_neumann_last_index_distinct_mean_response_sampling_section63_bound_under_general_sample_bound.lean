-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:24:03.346767+00:00
-- url     : https://prove2.me/submissions/795d4463-7dff-41dd-b2a1-3e8654a966b6

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

set_option maxHeartbeats 1600000

open MatrixCompletion
open scoped Matrix.Norms.L2Operator

/-!
Source: Candès–Recht 2008, Section 6.3, PDF p. 33, the second subterm of the
`ω₁ = ω₂ ≠ ω₃` case (mean response part), controlled by Theorem 6.3 applied to
the rescaled sign matrix and Lemma 6.4 for the off-diagonal response operator.

## SOUND `r/min` reroute (this file)

The previous version of this Sol routed through the DISPROVED `r/max`
response-operator node `quadratic_neumann_last_index_distinct_response_operator_bound`
(3cd3acbe) via the immutable rate engine
`response_centered_sampling_quadratic_mean_rate_bound_from_rescaled_sign_event`
(whose response hypothesis is `r/max`).  That was a false reduction: the
`r/max` bound is FALSE on thin matrices (single-entry `2×N` counterexample; the
tangent kernel is governed by `min(n₁,n₂)`, CR eqs (4.7)–(4.8)).

This file instead consumes the SOUND corrected `r/min` node
`quadratic_neumann_last_index_distinct_response_operator_bound_min_dim`
(Lemma 6.4 at the correct `min` denominator) and inlines the (linear)
response-transfer chain directly, so the whole reduction routes only through
Proved/corrected nodes.  The `r/min` factor still absorbs into the four-term
§6.3 summary scale `Φ` (term₄): the sign matrix supplies the `√(r/(n₁n₂))`
normalization, so `μ₀·(r/min)·√(βNlogN/p)·p⁻¹·μ₁√(r/nn) ≤ term₄` on the whole
feasible regime (numerically verified worst ≈ 0.05·Φ, thin-ridge included).
-/

-- spectralNorm helpers --------------------------------------------------------

private theorem spectralNorm_nonneg {n1 n2 : Nat} (A : RealMatrix n1 n2) :
    0 ≤ spectralNorm A := norm_nonneg _

private theorem spectralNorm_smul {n1 n2 : Nat} (c : ℝ) (A : RealMatrix n1 n2) :
    spectralNorm (c • A) = |c| * spectralNorm A := by
  unfold spectralNorm
  rw [show Matrix.toEuclideanLin (c • A) = c • (Matrix.toEuclideanLin A) from map_smul _ _ _]
  rw [show LinearMap.toContinuousLinearMap (c • (Matrix.toEuclideanLin A))
      = c • (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) from map_smul _ _ _]
  rw [norm_smul]; simp [Real.norm_eq_abs]

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma abs_entry_le_entrySupNorm {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Finite.le_ciSup_of_le i (Finite.le_ciSup_of_le j le_rfl)

private lemma entrySupNorm_smul_le_of_nonneg {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (c : ℝ) (hc : 0 ≤ c) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm (c • X) ≤ c * entrySupNorm X := by
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  calc
    |(c • X) i j| = |c| * |X i j| := by simp [abs_mul]
    _ = c * |X i j| := by rw [abs_of_nonneg hc]
    _ ≤ c * entrySupNorm X := mul_le_mul_of_nonneg_left (abs_entry_le_entrySupNorm X i j) hc

-- general-sample-bound → βNlogN fixed-matrix lower bound ----------------------

private lemma general_sample_bound_implies_fixed_matrix_sample_lower
    {C' β μ₀ μ₁ : ℝ} {n₁ n₂ r m : ℕ}
    (hC' : 1 ≤ C') (hβ : 2 < β)
    (hn₁ : 0 < n₁) (hr : 0 < r)
    (hμ₁ : 1 ≤ μ₁)
    (hmLower :
      (m : ℝ) ≥
        C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
          * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂)))) :
    (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  let K : ℝ :=
    max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
      (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
  let N : ℝ := (↑(max n₁ n₂) : ℝ)
  let R : ℝ := (r : ℝ)
  let L : ℝ := β * Real.log N
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_one : 1 ≤ N := by
    dsimp [N]; exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hlog_nonneg : 0 ≤ Real.log N := Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hR_one : 1 ≤ R := by dsimp [R]; exact_mod_cast (Nat.succ_le_of_lt hr)
  have hK_one : 1 ≤ K := by
    have hμ₁sq : 1 ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
    exact le_trans hμ₁sq
      (by dsimp [K]; exact le_trans (le_max_left _ _) (le_max_left _ _))
  have hprod : L * N ≤ C' * K * N * R * L := by
    calc
      L * N = (1 * 1 * N * 1 * L) := by ring
      _ ≤ C' * K * N * R * L := by gcongr
  have hmLower' : (m : ℝ) ≥ C' * K * N * R * L := by
    simpa [K, N, R, L, mul_assoc] using hmLower
  calc
    β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))
        = L * N := by simp [L, N, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ C' * K * N * R * L := hprod
    _ ≤ (m : ℝ) := hmLower'

-- arithmetic bridge: the per-index rate (at the `min` denominator) ≤ term₄ -----
-- rate = μ₀·(R/mn)·√(N·βL/p)·p⁻¹·μ₁·√(R/nn) ,  mn = min, N = max, nn = N·mn.

private lemma rate_le_term4_min
    (μ₀ μ₁ N R βL p nn mn M : ℝ)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hN : 0 < N) (hR : 0 < R) (hM : 0 < M) (hmn : 0 < mn)
    (hmnN : mn ≤ N) (hβL : 1 ≤ βL) (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) :
    μ₀ * (R / mn) * Real.sqrt (N * βL / p) * p⁻¹ * μ₁ * Real.sqrt (R / nn) ≤
      Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3 : ℝ) / 2) := by
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hβL0 : 0 < βL := lt_of_lt_of_le one_pos hβL
  set Q : ℝ := μ₀ * (R / mn) * Real.sqrt (N * βL / p) * p⁻¹ * μ₁ * Real.sqrt (R / nn) with hQ
  set T : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3 : ℝ) / 2) with hT
  have hQnn : 0 ≤ Q := by rw [hQ]; positivity
  have hTnn : 0 ≤ T := by rw [hT]; apply Real.rpow_nonneg; positivity
  have hbase_pos : 0 < (μ₀ * μ₁ * N * R * βL) / M := by positivity
  have hTsq : T ^ 2 = N ^ 3 * R ^ 3 * βL ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 / M ^ 3 := by
    have hTbase : T ^ 2 = ((μ₀ * μ₁ * N * R * βL) / M) ^ 3 := by
      rw [hT]
      have h1 : (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)) ^ (2:ℕ)
          = (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ) :=
        (Real.rpow_natCast _ 2).symm
      have h2 : (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ)
          = Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) (((3:ℝ)/2) * ((2:ℕ):ℝ)) :=
        (Real.rpow_mul (le_of_lt hbase_pos) _ _).symm
      rw [h1, h2, show ((3:ℝ)/2) * ((2:ℕ):ℝ) = ((3:ℕ):ℝ) by norm_num]
      exact Real.rpow_natCast _ 3
    rw [hTbase]
    have hMne : M ≠ 0 := ne_of_gt hM
    field_simp
  have hsqrt1 : Real.sqrt (N * βL / p) ^ 2 = N * βL / p := Real.sq_sqrt (by positivity)
  have hsqrt2 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
  have hQsq : Q ^ 2 = N ^ 3 * R ^ 3 * βL * μ₀ ^ 2 * μ₁ ^ 2 / M ^ 3 := by
    have hstep : Q ^ 2 = (μ₀ * (R / mn)) ^ 2 * (Real.sqrt (N * βL / p)) ^ 2 * (p⁻¹) ^ 2
        * μ₁ ^ 2 * (Real.sqrt (R / nn)) ^ 2 := by rw [hQ]; ring
    rw [hstep, hsqrt1, hsqrt2, hp, hnn]
    have hNne : N ≠ 0 := ne_of_gt hN
    have hMne : M ≠ 0 := ne_of_gt hM
    have hmnne : mn ≠ 0 := ne_of_gt hmn
    field_simp
  have hQsq_le_Tsq : Q ^ 2 ≤ T ^ 2 := by
    rw [hQsq, hTsq]
    have hnum : N ^ 3 * R ^ 3 * βL * μ₀ ^ 2 * μ₁ ^ 2
        ≤ N ^ 3 * R ^ 3 * βL ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 := by
      have hkey : (1 : ℝ) ≤ βL ^ 2 * μ₀ * μ₁ := by
        have hβLsq : (1:ℝ) ≤ βL ^ 2 := by nlinarith [hβL, hβL0]
        calc (1:ℝ) = 1 * 1 * 1 := by ring
          _ ≤ βL ^ 2 * μ₀ * μ₁ := by gcongr
      have hpref : 0 ≤ N ^ 3 * R ^ 3 * βL * μ₀ ^ 2 * μ₁ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hpref]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  nlinarith [hQsq_le_Tsq, hQnn, hTnn, sq_nonneg (T - Q)]

-- (n₁ : ℝ)*(n₂ : ℝ) = max·min --------------------------------------------------

private lemma prod_eq_max_mul_min (n₁ n₂ : ℕ) :
    ((n₁ : ℝ) * (n₂ : ℝ)) = ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ := max_mul_min n₁ n₂
  have : ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hprod_nat
  linarith [this]

set_option maxHeartbeats 1600000 in
theorem solution :
    ∃ Cresp cresp : ℝ, 0 < Cresp ∧ 0 < cresp ∧
      ∀ C' : ℝ, Cresp ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                ((1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
                  quadraticLastIndexDistinctOffDiagonalResponse S
                    (centeredSamplingFluctuation Omega
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                      ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                        signMatrix S))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cresp *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - cresp * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with ⟨Cfixed, hCfixed, hFixed⟩
  rcases quadratic_neumann_last_index_distinct_response_operator_bound_min_dim with
    ⟨CrespOp, hCrespOp, hRop⟩
  refine ⟨max 1 (CrespOp * Cfixed), 1, ?_, one_pos, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set Cout : ℝ := max 1 (CrespOp * Cfixed) with hCout
  have hCfixed0 : 0 ≤ Cfixed := le_of_lt hCfixed
  have hCrespOp0 : 0 ≤ CrespOp := le_of_lt hCrespOp
  have hCrC0 : 0 ≤ CrespOp * Cfixed := by positivity
  have hCrC_le : CrespOp * Cfixed ≤ Cout := le_max_right _ _
  have hCout_nonneg : 0 ≤ Cout := le_trans zero_le_one (le_max_left _ _)
  -- basic positivity
  have hN_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_nat
  have hN_one : 1 ≤ N := by rw [hN]; exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hR_pos : 0 < R := by rw [hR]; exact_mod_cast hr
  have hlogN_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  obtain ⟨hp0, hp1⟩ : 0 ≤ p ∧ p ≤ 1 := by
    constructor
    · rw [hp]; positivity
    · rw [hp, div_le_one (by positivity)]
      have : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hm
      exact this
  have hOne_le : (1 : ℝ) ≤ C' := le_trans (le_max_left _ _) hC'
  -- fixed-matrix sample lower bound
  have hSampleFixed :
      (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    general_sample_bound_implies_fixed_matrix_sample_lower hOne_le hβ hn₁ hr hμ₁ hmLower
  -- the response-operator bound (r/min, SOUND) as an abbreviation
  have hRopBound :
      ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X) ≤
          CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) * spectralNorm X := by
    intro X
    exact hRop n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 X
  -- the fixed-matrix high-probability event at the tight entry scale
  have hFixedProb :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p (p⁻¹ • signMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (p⁻¹ • signMatrix S))) ≥
        1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [hp] using
      hFixed β hβ n₁ n₂ m (p⁻¹ • signMatrix S) hn₁ hn₂ hm hSampleFixed
  refine le_trans hFixedProb ?_
  refine bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
    (fun Omega =>
      CenteredSamplingSpectralBound Omega p (p⁻¹ • signMatrix S)
        (Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm (p⁻¹ • signMatrix S)))
    (fun Omega =>
      spectralNorm
        ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S
          (centeredSamplingFluctuation Omega p (p⁻¹ • signMatrix S))) ≤ _)
    hp0 hp1 ?_
  intro Omega hΩ
  rw [CenteredSamplingSpectralBound] at hΩ
  -- hΩ : spectralNorm (fluctuation Ω p (p⁻¹•E)) ≤ Cfixed·√(βNlogN/p)·entrySup(p⁻¹•E)
  set Fluct : Matrix (Fin n₁) (Fin n₂) ℝ :=
    centeredSamplingFluctuation Omega p (p⁻¹ • signMatrix S) with hFluct
  -- bound the entrySup factor
  have hSignBound : entrySupNorm (signMatrix S) ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hpinv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  have hEntry :
      entrySupNorm (p⁻¹ • signMatrix S) ≤
        p⁻¹ * (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
    calc entrySupNorm (p⁻¹ • signMatrix S)
        ≤ p⁻¹ * entrySupNorm (signMatrix S) :=
          entrySupNorm_smul_le_of_nonneg hn₁ hn₂ p⁻¹ hpinv_nonneg (signMatrix S)
      _ ≤ p⁻¹ * (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) :=
          mul_le_mul_of_nonneg_left hSignBound hpinv_nonneg
  -- Split on whether 1 ≤ β·logN (i.e. N ≥ 2), else rate collapses to 0.
  by_cases hβL : 1 ≤ β * logN
  · -- main case
    have hβlog_pos : 0 < β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
      rw [← hN, ← hlogN]
      have : 0 < N * (β * logN) := by
        have := lt_of_lt_of_le one_pos hβL; positivity
      nlinarith [this, hN_pos, lt_of_lt_of_le one_pos hβL]
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hmz | hmp
      · exfalso
        have hzero : ((m : ℝ)) = 0 := by rw [hmz]; norm_num
        rw [hzero] at hSampleFixed; linarith [hSampleFixed, hβlog_pos]
      · exact hmp
    have hMobs_pos : 0 < Mobs := by rw [hMobs]; exact_mod_cast hm_pos
    have hp_pos : 0 < p := by rw [hp]; positivity
    -- spectralNorm ((1-p)•Rop(Fluct)) = (1-p)·spectralNorm(Rop(Fluct))
    have h1p_nonneg : 0 ≤ 1 - p := by linarith [hp1]
    have hspec_smul :
        spectralNorm ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S Fluct) =
          (1 - p) * spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct) := by
      rw [spectralNorm_smul, abs_of_nonneg h1p_nonneg]
    -- Rop bound applied to the fluctuation
    have hRopFluct :
        spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤
          CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) * spectralNorm Fluct :=
      hRopBound Fluct
    -- combine with the fixed-matrix fluctuation bound
    have hfixed_factor_nonneg :
        0 ≤ Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) := by positivity
    have hFluctBound :
        spectralNorm Fluct ≤
          Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
            entrySupNorm (p⁻¹ • signMatrix S) := by
      simpa [hFluct] using hΩ
    have hRminScale_nonneg :
        0 ≤ CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      have : 0 < min n₁ n₂ := lt_min hn₁ hn₂
      have hmincast : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by exact_mod_cast this
      positivity
    -- chain: spectralNorm(Rop Fluct) ≤ CrespOp·μ₀·(R/min)·(Cfixed·√(...)·entrySup(p⁻¹•E))
    have hRopFluct' :
        spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤
          CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
              entrySupNorm (p⁻¹ • signMatrix S)) := by
      refine le_trans hRopFluct ?_
      exact mul_le_mul_of_nonneg_left hFluctBound hRminScale_nonneg
    -- refine the entrySup factor and rewrite into the analytic rate shape
    have hRHS_le :
        CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
              entrySupNorm (p⁻¹ • signMatrix S)) ≤
          (CrespOp * Cfixed) *
            (μ₀ * (R / ((min n₁ n₂ : ℕ) : ℝ)) * Real.sqrt (N * (β * logN) / p) * p⁻¹ *
              μ₁ * Real.sqrt (R / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
      have hbaseFactor_nonneg :
          0 ≤ CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p)) := by
        have : 0 < min n₁ n₂ := lt_min hn₁ hn₂
        have hmincast : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by exact_mod_cast this
        positivity
      have hEntry' :
          entrySupNorm (p⁻¹ • signMatrix S) ≤
            p⁻¹ * (μ₁ * Real.sqrt (R / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
        rw [hR]; exact hEntry
      have hstep :
          CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (p⁻¹ • signMatrix S)) =
            (CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p))) *
              entrySupNorm (p⁻¹ • signMatrix S) := by ring
      rw [hstep]
      calc
        (CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p))) *
              entrySupNorm (p⁻¹ • signMatrix S)
            ≤ (CrespOp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p))) *
                (p⁻¹ * (μ₁ * Real.sqrt (R / ((n₁ : ℝ) * (n₂ : ℝ))))) :=
              mul_le_mul_of_nonneg_left hEntry' hbaseFactor_nonneg
        _ = (CrespOp * Cfixed) *
              (μ₀ * (R / ((min n₁ n₂ : ℕ) : ℝ)) * Real.sqrt (N * (β * logN) / p) * p⁻¹ *
                μ₁ * Real.sqrt (R / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            have hsqrteq :
                Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) =
                  Real.sqrt (N * (β * logN) / p) := by
              rw [hN, hlogN]; congr 1; ring
            rw [hsqrteq, hR]
            ring
    -- rate_le_term4_min gives the inner factor ≤ term₄
    have hmn_pos : 0 < ((min n₁ n₂ : ℕ) : ℝ) := by
      have : 0 < min n₁ n₂ := lt_min hn₁ hn₂; exact_mod_cast this
    have hmnN : ((min n₁ n₂ : ℕ) : ℝ) ≤ N := by
      rw [hN]; exact_mod_cast (min_le_max : min n₁ n₂ ≤ max n₁ n₂)
    have hnn_eq : (n₁ : ℝ) * (n₂ : ℝ) = N * ((min n₁ n₂ : ℕ) : ℝ) := by
      rw [hN]; exact prod_eq_max_mul_min n₁ n₂
    have hp_eq : p = Mobs / ((n₁ : ℝ) * (n₂ : ℝ)) := by rw [hp, hMobs]
    have hinner :=
      rate_le_term4_min μ₀ μ₁ N R (β * logN) p ((n₁ : ℝ) * (n₂ : ℝ))
        ((min n₁ n₂ : ℕ) : ℝ) Mobs hnn_eq hp_eq hN_pos hR_pos hMobs_pos hmn_pos
        hmnN hβL hμ₀ hμ₁
    -- assemble: spectralNorm(Rop Fluct) ≤ (CrespOp·Cfixed)·term₄
    have hstep1 :
        spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤
          (CrespOp * Cfixed) *
            Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) := by
      refine le_trans hRopFluct' (le_trans hRHS_le ?_)
      exact mul_le_mul_of_nonneg_left hinner hCrC0
    -- (1-p) factor
    have hspec_le :
        spectralNorm ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤
          (CrespOp * Cfixed) *
            Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) := by
      rw [hspec_smul]
      calc (1 - p) * spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct)
          ≤ 1 * ((CrespOp * Cfixed) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)) := by
            apply mul_le_mul _ hstep1 (spectralNorm_nonneg _) (by norm_num)
            linarith [hp0]
        _ = (CrespOp * Cfixed) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) := by ring
    -- term₄ ≤ Φ
    set term₁ : ℝ :=
      (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 with ht1
    set term₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 with ht2
    set term₃ : ℝ :=
      Real.sqrt (β * logN) * Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) with ht3
    set term₄ : ℝ :=
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) with ht4
    have h1n : 0 ≤ term₁ := by rw [ht1]; positivity
    have h2n : 0 ≤ term₂ := by rw [ht2]; positivity
    have h3n : 0 ≤ term₃ := by
      rw [ht3]; apply mul_nonneg; apply mul_nonneg
      · positivity
      · apply Real.rpow_nonneg; positivity
      · positivity
    have h4n : 0 ≤ term₄ := by rw [ht4]; apply Real.rpow_nonneg; positivity
    have hΦpos : term₄ ≤ term₁ + term₂ + term₃ + term₄ := by linarith
    have hCscale_term4_le :
        (CrespOp * Cfixed) * term₄ ≤ Cout * (term₁ + term₂ + term₃ + term₄) := by
      calc (CrespOp * Cfixed) * term₄ ≤ Cout * term₄ :=
            mul_le_mul_of_nonneg_right hCrC_le h4n
        _ ≤ Cout * (term₁ + term₂ + term₃ + term₄) :=
            mul_le_mul_of_nonneg_left hΦpos hCout_nonneg
    have hfinal :
        spectralNorm ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤
          Cout * (term₁ + term₂ + term₃ + term₄) :=
      le_trans hspec_le hCscale_term4_le
    show spectralNorm _ ≤ _
    simpa [hFluct, hCout, hN, hR, hMobs, hlogN, ht1, ht2, ht3, ht4] using hfinal
  · -- edge case: β·logN < 1 ⟹ N = 1 ⟹ logN = 0 ⟹ fluctuation-bound = 0 ⟹ response = 0
    have hβLsmall : β * logN < 1 := lt_of_not_ge hβL
    have hlogN_lt : logN < 1 / 2 := by
      by_contra hle
      push_neg at hle
      have : (1 : ℝ) ≤ β * logN := by nlinarith [hβ, hle, hlogN_nonneg]
      linarith [hβLsmall, this]
    have hN_lt2 : N < 2 := by
      by_contra hge
      push_neg at hge
      have : Real.log 2 ≤ logN := by rw [hlogN]; exact Real.log_le_log (by norm_num) hge
      have hlog2 : (0.6931 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; norm_num at this ⊢; linarith [this]
      linarith [hlogN_lt, this, hlog2]
    have hN_eq1 : N = 1 := by
      have hNnat_le : max n₁ n₂ < 2 := by
        by_contra hh
        push_neg at hh
        have : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hh
        linarith [hN_lt2, this]
      have : max n₁ n₂ = 1 := by omega
      rw [hN, this]; norm_num
    have hlogN_zero : logN = 0 := by rw [hlogN, hN_eq1]; simp
    have hsqrt_zero :
        Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) = 0 := by
      have : (β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) = 0 := by
        rw [← hN, ← hlogN, hlogN_zero]; ring
      rw [this]; simp
    -- fluctuation bound = 0
    have hFluct0 : spectralNorm Fluct ≤ 0 := by
      have hz : Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm (p⁻¹ • signMatrix S) = 0 := by rw [hsqrt_zero]; ring
      have : spectralNorm Fluct ≤ Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm (p⁻¹ • signMatrix S) := by simpa [hFluct] using hΩ
      rw [hz] at this; exact this
    have hFluct_eq0 : spectralNorm Fluct = 0 :=
      le_antisymm hFluct0 (spectralNorm_nonneg _)
    have h1p_nonneg : 0 ≤ 1 - p := by linarith [hp1]
    -- response of a zero-norm matrix is bounded by CrespOp·μ₀·(R/min)·0 = 0
    have hRop0 :
        spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤ 0 := by
      have := hRopBound Fluct
      rw [hFluct_eq0] at this; simpa using this
    have hspec_le0 :
        spectralNorm ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤ 0 := by
      rw [spectralNorm_smul, abs_of_nonneg h1p_nonneg]
      have := mul_le_mul_of_nonneg_left hRop0 h1p_nonneg
      simpa using this
    show spectralNorm _ ≤ _
    have hgoal : spectralNorm
        ((1 - p) • quadraticLastIndexDistinctOffDiagonalResponse S Fluct) ≤ 0 := by
      simpa [hFluct] using hspec_le0
    refine le_trans (by simpa [hFluct] using hgoal) ?_
    -- Φ ≥ 0
    have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
    have hlog_cast_nonneg : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) := by
      rw [← hN, ← hlogN]; exact hlogN_nonneg
    simp only
    rw [hCout, hN, hR, hMobs]
    apply mul_nonneg hCout_nonneg
    have hbaseN_nonneg : 0 ≤ ((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) := by positivity
    have hbase4_nonneg :
        0 ≤ (μ₀ * μ₁ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ)) / (m : ℝ)) := by positivity
    have ht1 : 0 ≤
        μ₀ ^ 2 * μ₁ *
          Real.sqrt (((↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ)) *
          (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) ^ 2) := by positivity
    have ht2 : 0 ≤
        μ₀ ^ 2 * (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) ^ 2) := by positivity
    have ht3 : 0 ≤
        Real.sqrt (β * Real.log (↑(max n₁ n₂) : ℝ)) *
          Real.rpow (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ))) ((3 : ℝ) / 2) *
          (μ₀ ^ 2 * (r : ℝ)) := by
      have := Real.rpow_nonneg hbaseN_nonneg ((3 : ℝ) / 2); positivity
    have ht4 : 0 ≤
        Real.rpow
          ((μ₀ * μ₁ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ))
          ((3 : ℝ) / 2) := Real.rpow_nonneg hbase4_nonneg _
    nlinarith
