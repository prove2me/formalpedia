-- Prove2me | solution 1 for FedAvg.ConvexFedAvgConvergence
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-23T03:17:38.517631+00:00
-- url     : https://prove2.me/submissions/cc8606aa-de01-48bc-bdf5-19a3b47e53e4

import Definitions.Def_FedAvg_Model
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Theorems.Thm_FedAvg_PerRoundProgress
import Theorems.Thm_FedAvg_BoundedClientDrift

/-!
Integrability bridges for Wang et al., *A Field Guide to Federated Optimization*,
Section 6.1.1, PDF p. 40, equations (11)--(14), and Appendix D, PDF pp. 86--88.
These are formal analytic bookkeeping for the stated stochastic model, not new
probabilistic assumptions. Mathlib's mean-value bound and L2 integrability API
supply the growth and moment estimates.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace FedAvg

variable {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem d M} {τ T : ℕ} {η : ℝ}

theorem shadow_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k ≤ τ) :
    MemLp (shadow R t k) 2 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ ↦
    R.x_squareIntegrable t ht k hk i)).const_smul (M : ℝ)⁻¹

theorem shadowDistanceSq_integrable (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k ≤ τ) : Integrable (shadowDistanceSq R t k) μ := by
  exact ((shadow_memLp R ht hk).sub (memLp_const P.xstar)).norm.integrable_sq

theorem clientDriftSq_integrable (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k ≤ τ) (i : Fin M) : Integrable (clientDriftSq R t k i) μ := by
  exact ((R.x_squareIntegrable t ht k hk i).sub
    (shadow_memLp R ht hk)).norm.integrable_sq

theorem Problem.norm_gradient_le (P : Problem d M) (i : Fin M) (x : ModelSpace d) :
    ‖gradient (P.f i) x‖ ≤ P.L * ‖x‖ + ‖gradient (P.f i) 0‖ := by
  calc
    ‖gradient (P.f i) x‖ ≤
        ‖gradient (P.f i) x - gradient (P.f i) 0‖ + ‖gradient (P.f i) 0‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ P.L * ‖x‖ + ‖gradient (P.f i) 0‖ := by
      simpa using add_le_add_right (P.smooth i x 0) ‖gradient (P.f i) 0‖

theorem Problem.norm_f_le (P : Problem d M) (i : Fin M) (x : ModelSpace d) :
    ‖P.f i x‖ ≤ ‖P.f i 0‖ + ‖gradient (P.f i) 0‖ * ‖x‖ + P.L * ‖x‖ ^ 2 := by
  have hb : ∀ y ∈ Metric.closedBall (0 : ModelSpace d) ‖x‖,
      ‖InnerProductSpace.toDual ℝ (ModelSpace d) (gradient (P.f i) y)‖ ≤
        P.L * ‖x‖ + ‖gradient (P.f i) 0‖ := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_zero_right] at hy
    simpa using (P.norm_gradient_le i y).trans
      (add_le_add (mul_le_mul_of_nonneg_left hy P.smoothness_pos.le) le_rfl)
  have hmv : ‖P.f i x - P.f i 0‖ ≤
      (P.L * ‖x‖ + ‖gradient (P.f i) 0‖) * ‖x - 0‖ :=
    (convex_closedBall (0 : ModelSpace d) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ ↦ (P.hasGradient i y).hasFDerivAt.hasFDerivWithinAt) hb
      (by simp) (by simp)
  have htriangle := norm_le_norm_sub_add (P.f i x) (P.f i 0)
  simp only [sub_zero] at hmv
  nlinarith

omit [StandardBorelSpace Ω] in
theorem f_integrable_comp (P : Problem d M) (i : Fin M) {X : Ω → ModelSpace d}
    (hX : MemLp X 2 μ) : Integrable (fun ω ↦ P.f i (X ω)) μ := by
  have hf : Continuous (P.f i) := continuous_iff_continuousAt.mpr
    (fun x ↦ (P.hasGradient i x).hasFDerivAt.continuousAt)
  have hb : Integrable (fun ω ↦ ‖P.f i 0‖ + ‖gradient (P.f i) 0‖ * ‖X ω‖ +
      P.L * ‖X ω‖ ^ 2) μ :=
    ((integrable_const _).add ((hX.integrable (by norm_num)).norm.const_mul _)).add
      (hX.norm.integrable_sq.const_mul _)
  exact hb.mono' (hf.comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω ↦ P.norm_f_le i (X ω)))

omit [StandardBorelSpace Ω] in
theorem objective_integrable_comp (P : Problem d M) {X : Ω → ModelSpace d}
    (hX : MemLp X 2 μ) : Integrable (fun ω ↦ objective P.f (X ω)) μ := by
  exact (integrable_finsetSum Finset.univ (fun i _ ↦ f_integrable_comp P i hX)).const_mul _

theorem roundLoss_integrable (R : Run P μ τ T η) {t : ℕ} (ht : t < T) :
    Integrable (roundLoss R t) μ := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro k hk
  exact (objective_integrable_comp P (shadow_memLp R ht
    (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))).sub (integrable_const _)

theorem avgLoss_integrable (R : Run P μ τ T η) : Integrable (avgLoss R) μ := by
  exact (integrable_finsetSum (Finset.range T) (fun t ht ↦
    roundLoss_integrable R (Finset.mem_range.mp ht))).const_mul _

theorem progressRHS_integrable (R : Run P μ τ T η) {t : ℕ} (ht : t < T) :
    Integrable (progressRHS R t) μ := by
  apply Integrable.add
  · exact ((shadowDistanceSq_integrable R ht (Nat.zero_le τ)).sub
      integrable_condExp).div_const _
  · apply Integrable.add (integrable_const _)
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum (Finset.range τ) (fun k _ ↦ integrable_condExp))

theorem shadow_initial (R : Run P μ τ T η) (ω : Ω) : shadow R 0 0 ω = P.x0 := by
  simp only [shadow, R.initial, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ M, ← smul_assoc]
  simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.clients_pos)]

theorem shadow_synchronize (R : Run P μ τ T η) {t : ℕ} (ht : t + 1 < T) :
    shadow R (t + 1) 0 =ᵐ[μ] shadow R t τ := by
  filter_upwards [Filter.eventually_all.mpr (R.synchronize t ht)] with ω hω
  simp only [shadow, hω, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ M, ← smul_assoc]
  simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.clients_pos)]

theorem shadowDistanceSq_initial (R : Run P μ τ T η) :
    shadowDistanceSq R 0 0 = fun _ ↦ distance P ^ 2 := by
  funext ω
  simp [shadowDistanceSq, shadow_initial, distance]

theorem shadowDistanceSq_synchronize (R : Run P μ τ T η) {t : ℕ} (ht : t + 1 < T) :
    shadowDistanceSq R (t + 1) 0 =ᵐ[μ] shadowDistanceSq R t τ := by
  filter_upwards [shadow_synchronize R ht] with ω hω
  simp only [shadowDistanceSq, hω]

end FedAvg


/-!
Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1,
Section 6.1.2, PDF p. 41, Theorem 1 equation (15): integrate Lemmas 1–2
and telescope the squared-distance potential across synchronized rounds.
These helpers prove the reduction; the source lemmas remain separate targets.
-/
open MeasureTheory
open scoped BigOperators
namespace FedAvg

lemma sum_dissipation_le (A Z : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hZ : ∀ n < N, 0 ≤ Z n)
    (hAZ : ∀ n, n + 1 < N → A (n + 1) = Z n) :
    ∑ n ∈ Finset.range N, (A n - Z n) ≤ A 0 := by
  have exact_sum : ∀ n, 0 < n → n ≤ N →
      ∑ i ∈ Finset.range n, (A i - Z i) = A 0 - Z (n - 1) := by
    intro n hn hnN
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hz : n = 0
      · subst n; simp
      · rw [Finset.sum_range_succ, ih (by omega) (by omega)]
        have heq := hAZ (n - 1) (by omega)
        have hind : n - 1 + 1 = n := by omega
        rw [hind] at heq
        simp only [Nat.add_sub_cancel]
        rw [heq]
        ring
  rw [exact_sum N hN le_rfl]
  exact sub_le_self _ (hZ (N - 1) (by omega))

variable {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Problem d M} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {τ T : ℕ} {η : ℝ}

lemma deviationTerm_le_of_drift (R : Run P μ τ T η) (t : ℕ)
    (hτ : 0 < τ)
    (h : ∀ k, k < τ → ∀ i,
      μ[clientDriftSq R t k i | R.history (t * τ)] ≤ᵐ[μ] fun _ ↦ driftRHS P τ η) :
    deviationTerm R t ≤ᵐ[μ] fun _ ↦ η * P.σ ^ 2 / M + P.L * driftRHS P τ η := by
  have hall : ∀ᵐ ω ∂μ, ∀ k, k < τ → ∀ i,
      μ[clientDriftSq R t k i | R.history (t * τ)] ω ≤ driftRHS P τ η := by
    simpa only [ae_all_iff] using h
  filter_upwards [hall] with ω hω
  unfold deviationTerm
  apply add_le_add_right
  have hsum : (∑ i : Fin M, ∑ k ∈ Finset.range τ,
      μ[clientDriftSq R t k i | R.history (t * τ)] ω) ≤
      (M : ℝ) * τ * driftRHS P τ η := by
    calc
      _ ≤ ∑ i : Fin M, ∑ k ∈ Finset.range τ, driftRHS P τ η :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k hk ↦ hω k (Finset.mem_range.mp hk) i
      _ = _ := by simp; ring
  have hL := P.smoothness_pos
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.clients_pos)
  have ht : (τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hτ)
  calc
    _ ≤ P.L / ((M : ℝ) * τ) * ((M : ℝ) * τ * driftRHS P τ η) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

lemma expected_roundLoss_le (R : Run P μ τ T η) (t : ℕ)
    (hτ : 0 < τ)
    (hstart : Integrable (shadowDistanceSq R t 0) μ)
    (hprogress : μ[roundLoss R t | R.history (t * τ)] ≤ᵐ[μ] progressRHS R t)
    (hdrift : ∀ k, k < τ → ∀ i,
      μ[clientDriftSq R t k i | R.history (t * τ)] ≤ᵐ[μ] fun _ ↦ driftRHS P τ η) :
    (∫ ω, roundLoss R t ω ∂μ) ≤
      ((∫ ω, shadowDistanceSq R t 0 ω ∂μ) -
       (∫ ω, shadowDistanceSq R t τ ω ∂μ)) / (2 * η * τ) +
        (η * P.σ ^ 2 / M + P.L * driftRHS P τ η) := by
  have hdev := deviationTerm_le_of_drift R t hτ hdrift
  have hup : μ[roundLoss R t | R.history (t * τ)] ≤ᵐ[μ]
      fun ω ↦ progressTerm R t ω + (η * P.σ ^ 2 / M + P.L * driftRHS P τ η) := by
    filter_upwards [hprogress, hdev] with ω hp hd
    exact hp.trans (add_le_add_right hd _)
  have hint : Integrable (progressTerm R t) μ :=
    (hstart.sub integrable_condExp).div_const _
  have h := integral_mono_ae integrable_condExp (hint.add (integrable_const _)) hup
  rw [integral_condExp (R.history.le _)] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hint (integrable_const _)] at h
  unfold progressTerm at h
  rw [integral_div,
    integral_sub hstart integrable_condExp, integral_condExp (R.history.le _)] at h
  simpa using h

lemma convergence_from_round_estimates (R : Run P μ τ T η)
    (hτ : 0 < τ) (hT : 0 < T) (hη : 0 < η)
    (hloss : ∀ t, t < T → Integrable (roundLoss R t) μ)
    (hinitial : (∫ ω, shadowDistanceSq R 0 0 ω ∂μ) = distance P ^ 2)
    (hsync : ∀ t, t + 1 < T →
      (∫ ω, shadowDistanceSq R (t + 1) 0 ω ∂μ) =
      (∫ ω, shadowDistanceSq R t τ ω ∂μ))
    (hround : ∀ t, t < T → (∫ ω, roundLoss R t ω ∂μ) ≤
      ((∫ ω, shadowDistanceSq R t 0 ω ∂μ) -
       (∫ ω, shadowDistanceSq R t τ ω ∂μ)) / (2 * η * τ) +
        (η * P.σ ^ 2 / M + P.L * driftRHS P τ η)) :
    (∫ ω, avgLoss R ω ∂μ) ≤ convergenceRHS P τ T η := by
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum := sum_dissipation_le
    (fun t ↦ ∫ ω, shadowDistanceSq R t 0 ω ∂μ)
    (fun t ↦ ∫ ω, shadowDistanceSq R t τ ω ∂μ) T hT
    (fun t _ ↦ integral_nonneg fun ω ↦ sq_nonneg _) hsync
  dsimp only at hsum
  rw [hinitial] at hsum
  have hsumround := Finset.sum_le_sum (s := Finset.range T)
    (fun t ht ↦ hround t (Finset.mem_range.mp ht))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsumround
  have hdiv : (∑ t ∈ Finset.range T,
      ((∫ ω, shadowDistanceSq R t 0 ω ∂μ) - (∫ ω, shadowDistanceSq R t τ ω ∂μ))) /
      (2 * η * τ) ≤ distance P ^ 2 / (2 * η * τ) :=
    div_le_div_of_nonneg_right hsum (by positivity)
  have htot : (∑ t ∈ Finset.range T, ∫ ω, roundLoss R t ω ∂μ) ≤
      distance P ^ 2 / (2 * η * τ) +
        T * (η * P.σ ^ 2 / M + P.L * driftRHS P τ η) := by
    calc
      _ ≤ distance P ^ 2 / (2 * η * τ) +
          (T * (η * P.σ ^ 2) / M + T * (P.L * driftRHS P τ η)) :=
        hsumround.trans (add_le_add_left hdiv _)
      _ = _ := by ring
  unfold avgLoss
  rw [integral_const_mul, integral_finsetSum _ (fun t ht ↦ hloss t (Finset.mem_range.mp ht))]
  calc
    _ ≤ (T : ℝ)⁻¹ * (distance P ^ 2 / (2 * η * τ) +
        T * (η * P.σ ^ 2 / M + P.L * driftRHS P τ η)) :=
      mul_le_mul_of_nonneg_left htot (by positivity)
    _ = convergenceRHS P τ T η := by
      unfold convergenceRHS driftRHS
      field_simp
      ring

end FedAvg

open FedAvg
universe u
theorem solution :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ T : ℕ) (η : ℝ),
    0 < τ → 0 < T → 0 < η → η ≤ 1 / (4 * P.L) →
    ∀ R : Run P μ τ T η, (∫ ω, avgLoss R ω ∂μ) ≤ convergenceRHS P τ T η := by
  intro d M P Ω _ _ μ _ τ T η hτ hT hη hηL R
  apply convergence_from_round_estimates R hτ hT hη
  · exact fun t ht ↦ roundLoss_integrable R ht
  · rw [shadowDistanceSq_initial]
    simp
  · exact fun t ht ↦ integral_congr_ae (shadowDistanceSq_synchronize R ht)
  · intro t ht
    exact expected_roundLoss_le R t hτ
      (shadowDistanceSq_integrable R ht (Nat.zero_le τ))
      (FedAvg.PerRoundProgress d M P Ω μ τ T η hτ hT hη hηL R t ht)
      (fun k hk i ↦ FedAvg.BoundedClientDrift d M P Ω μ τ T η hτ hT hη hηL R t ht
        k (Nat.le_of_lt hk) i)
