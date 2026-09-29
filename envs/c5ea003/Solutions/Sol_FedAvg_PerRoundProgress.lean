-- Prove2me | solution 1 for FedAvg.PerRoundProgress
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-23T04:02:20.242229+00:00
-- url     : https://prove2.me/submissions/b5e4d1ff-bc66-4c7d-9784-0e5b0bd0caf1

import Definitions.Def_FedAvg_Model
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.NormNum
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false

noncomputable section

/- Helpers from SmoothConvex. -/
section
open scoped BigOperators InnerProductSpace
open Set

namespace FedAvg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_line_deriv {f : E → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (x y : E) (t : ℝ) :
    HasDerivAt (f ∘ AffineMap.lineMap x y)
      ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ t := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap

/-- Convexity input in Appendix D.1, equation (25). -/
theorem convex_gradient_lower {f : E → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hc : ConvexOn ℝ univ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have hconv : ConvexOn ℝ univ (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)) := by
    simpa using hc.comp_affineMap (AffineMap.lineMap x y)
  have hs := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (mem_univ _) (mem_univ _) zero_lt_one (gradient_line_deriv hf x y 0)
  simp only [AffineMap.lineMap_apply_zero, slope_def_field, Function.comp_apply,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hs
  linarith

/-- The exact smoothness remainder used in Appendix D.1, equation (25). -/
theorem smooth_descent {f : E → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (_hL : 0 ≤ L)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  let a := ⟪gradient f x, y - x⟫_ℝ
  let b := L / 2 * ‖y - x‖ ^ 2
  let B : ℝ → ℝ := fun t ↦ f x + t * a + t ^ 2 * b
  have hBder (t : ℝ) : HasDerivAt B (a + 2 * t * b) t := by
    convert (((hasDerivAt_id t).mul_const a).const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const b) using 1
    simp
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ ≤ a + 2 * t * b := by
    have hn : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      simp [AffineMap.lineMap_apply_module', norm_smul, abs_of_nonneg ht.1]
    have hgrad := mul_le_mul_of_nonneg_right (hs (AffineMap.lineMap x y t) x)
      (norm_nonneg (y - x))
    have hi := real_inner_le_norm (gradient f (AffineMap.lineMap x y t) - gradient f x)
      (y - x)
    rw [hn] at hgrad
    rw [inner_sub_left] at hi
    dsimp [a, b]
    nlinarith
  have hfinal := image_le_of_deriv_right_le_deriv_boundary
    (f := f ∘ AffineMap.lineMap x y)
    (f' := fun t ↦ ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ)
    (a := 0) (b := 1)
    (by exact (continuous_iff_continuousAt.mpr fun t ↦
      (gradient_line_deriv hf x y t).continuousAt).continuousOn)
    (fun t _ ↦ (gradient_line_deriv hf x y t).hasDerivWithinAt)
    (B := B) (B' := fun t ↦ a + 2 * t * b)
    (by simp [B])
    (by exact (continuous_iff_continuousAt.mpr fun t ↦ (hBder t).continuousAt).continuousOn)
    (fun t _ ↦ (hBder t).hasDerivWithinAt) hbound
    (x := 1) (by simp)
  simpa [B, a, b] using hfinal

/-- The smooth convex gradient-gap inequality underlying Appendix D.2. -/
theorem smooth_convex_gap {f : E → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hc : ConvexOn ℝ univ f) (hL : 0 < L)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : E) :
    ‖gradient f x - gradient f y‖ ^ 2 ≤
      2 * L * (f x - f y - ⟪gradient f y, x-y⟫_ℝ) := by
  let v := gradient f x - gradient f y
  let z := x - L⁻¹ • v
  have hzx : z-x = -(L⁻¹ • v) := by dsimp [z]; abel
  have hzy : z-y = (x-y) - L⁻¹ • v := by dsimp [z]; abel
  have hdes := smooth_descent hf hL.le hs x z
  have hlo := convex_gradient_lower hf hc y z
  rw [hzx, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)] at hdes
  rw [hzy, inner_sub_right, inner_smul_right] at hlo
  have hv : ⟪gradient f x, v⟫_ℝ - ⟪gradient f y, v⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq v
  have heq : -(L⁻¹ * ⟪gradient f x, v⟫_ℝ) + L / 2 * (L⁻¹ * ‖v‖) ^ 2 +
      L⁻¹ * ⟪gradient f y, v⟫_ℝ = -(‖v‖ ^ 2 / (2 * L)) := by
    field_simp
    nlinarith [hv]
  have hgap : ‖v‖ ^ 2 / (2 * L) ≤ f x - f y - ⟪gradient f y, x-y⟫_ℝ := by
    linarith
  have hh := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hgap
  simpa only [mul_comm] using hh

/-- Cocoercivity used in Appendix D.2 immediately before equation (28). -/
theorem smooth_convex_cocoercive {f : E → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hc : ConvexOn ℝ univ f) (hL : 0 < L)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : E) :
    ‖gradient f x - gradient f y‖ ^ 2 ≤
      L * ⟪gradient f x - gradient f y, x-y⟫_ℝ := by
  have hxy := smooth_convex_gap hf hc hL hs x y
  have hyx := smooth_convex_gap hf hc hL hs y x
  rw [norm_sub_rev (gradient f y), show y-x = -(x-y) by abel, inner_neg_right] at hyx
  rw [inner_sub_left]
  nlinarith

namespace Problem

variable {d M : ℕ} (P : Problem d M)

theorem objective_hasGradient (x : ModelSpace d) :
    HasGradientAt (objective P.f) ((M : ℝ)⁻¹ • ∑ i, gradient (P.f i) x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [objective, map_smul, map_sum] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (P.hasGradient i x).hasFDerivAt)).const_mul (M : ℝ)⁻¹

theorem objective_gradient (x : ModelSpace d) :
    gradient (objective P.f) x = (M : ℝ)⁻¹ • ∑ i, gradient (P.f i) x :=
  (P.objective_hasGradient x).gradient

theorem objective_hasGradientAt (x : ModelSpace d) :
    HasGradientAt (objective P.f) (gradient (objective P.f) x) x := by
  rw [P.objective_gradient]
  exact P.objective_hasGradient x

theorem objective_convex : ConvexOn ℝ univ (objective P.f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    (P.convex i).2 (mem_univ x) (mem_univ y) ha hb hab)
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ) ≤ M))
  simpa only [objective, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    mul_add, mul_assoc, mul_left_comm (M : ℝ)⁻¹] using hh

theorem objective_smooth (x y : ModelSpace d) :
    ‖gradient (objective P.f) x - gradient (objective P.f) y‖ ≤ P.L * ‖x-y‖ := by
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.clients_pos)
  rw [P.objective_gradient x, P.objective_gradient y, ← smul_sub, ← Finset.sum_sub_distrib,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M))]
  calc
    (M : ℝ)⁻¹ * ‖∑ i, (gradient (P.f i) x - gradient (P.f i) y)‖
        ≤ (M : ℝ)⁻¹ * ∑ i, ‖gradient (P.f i) x - gradient (P.f i) y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg M))
    _ ≤ (M : ℝ)⁻¹ * ∑ _i : Fin M, (P.L * ‖x-y‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ P.smooth i x y)
        (inv_nonneg.mpr (Nat.cast_nonneg M))
    _ = P.L * ‖x-y‖ := by simp [← mul_assoc, hM]

theorem objective_lower (x y : ModelSpace d) :
    objective P.f x + ⟪gradient (objective P.f) x, y-x⟫_ℝ ≤ objective P.f y :=
  convex_gradient_lower P.objective_hasGradientAt P.objective_convex x y

theorem objective_descent (x y : ModelSpace d) :
    objective P.f y ≤ objective P.f x + ⟪gradient (objective P.f) x, y-x⟫_ℝ +
      P.L / 2 * ‖y-x‖ ^ 2 :=
  smooth_descent P.objective_hasGradientAt P.smoothness_pos.le P.objective_smooth x y

theorem objective_cocoercive (x y : ModelSpace d) :
    ‖gradient (objective P.f) x - gradient (objective P.f) y‖ ^ 2 ≤
      P.L * ⟪gradient (objective P.f) x - gradient (objective P.f) y, x-y⟫_ℝ :=
  smooth_convex_cocoercive P.objective_hasGradientAt P.objective_convex P.smoothness_pos
    P.objective_smooth x y

end Problem

end FedAvg
end

/- Helpers from ConditionalMoments. -/
section
/-! Conditional moment bridges for Wang et al., arXiv:2107.06917v1,
Appendix D.1, PDF pp. 86–87, equations (24)–(27), and Appendix D.2, pp. 87–88.
All cross terms below are justified by L2 integrability and conditional pull-out. -/

open MeasureTheory
open scoped InnerProductSpace
namespace FedAvg

variable {Ω E : Type*} {H : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
lemma inner_integrable_of_memLp {X Y : Ω → E} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ ⟪X ω, Y ω⟫_ℝ) μ := by
  have h := L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)
  apply h.congr
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hωX hωY
  simp only [hωX, hωY]

lemma condExp_inner_zero {X Z : Ω → E} (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hXm : AEStronglyMeasurable[H] X μ) (hZ0 : μ[Z | H] =ᵐ[μ] 0) :
    μ[fun ω ↦ ⟪X ω, Z ω⟫_ℝ | H] =ᵐ[μ] 0 := by
  have h := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hXm
    (inner_integrable_of_memLp hX hZ) (hZ.integrable (by norm_num))
  filter_upwards [h, hZ0] with ω hω h0
  simpa [h0] using hω

lemma condExp_norm_sq_add_centered (hm : H ≤ mΩ)
    {A Z : Ω → E} (hA : MemLp A 2 μ) (hZ : MemLp Z 2 μ)
    (hAm : AEStronglyMeasurable[H] A μ) (hZ0 : μ[Z | H] =ᵐ[μ] 0) (c : ℝ) :
    μ[fun ω ↦ ‖A ω + c • Z ω‖ ^ 2 | H] =ᵐ[μ]
      fun ω ↦ ‖A ω‖ ^ 2 + c ^ 2 * μ[fun ω ↦ ‖Z ω‖ ^ 2 | H] ω := by
  have hA2 := hA.norm.integrable_sq
  have hZ2 := hZ.norm.integrable_sq
  have hAZ := inner_integrable_of_memLp hA hZ
  have hinner := condExp_inner_zero hA hZ hAm hZ0
  have ha2m : AEStronglyMeasurable[H] (fun ω ↦ ‖A ω‖ ^ 2) μ := by
    exact ((continuous_norm : Continuous (fun x : E ↦ ‖x‖)).pow 2).comp_aestronglyMeasurable hAm
  have hself := condExp_of_aestronglyMeasurable' hm ha2m hA2
  have hlin₁ := condExp_add hA2 (hAZ.const_mul (2 * c)) H
  have hlin₂ := condExp_add (hA2.add (hAZ.const_mul (2 * c))) (hZ2.const_mul (c ^ 2)) H
  have hmul₁ := condExp_smul (μ := μ) (2 * c) (fun ω ↦ ⟪A ω, Z ω⟫_ℝ) H
  have hmul₂ := condExp_smul (μ := μ) (c ^ 2) (fun ω ↦ ‖Z ω‖ ^ 2) H
  have hexp : (fun ω ↦ ‖A ω + c • Z ω‖ ^ 2) =
      fun ω ↦ (‖A ω‖ ^ 2 + 2 * c * ⟪A ω, Z ω⟫_ℝ) + c ^ 2 * ‖Z ω‖ ^ 2 := by
    funext ω
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  rw [hexp]
  filter_upwards [hlin₁, hlin₂, hmul₁, hmul₂, hself, hinner] with ω h1 h2 h3 h4 h5 h6
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul, Pi.zero_apply] at h1 h2 h3 h4 h5 h6
  rw [h2, h1, h3, h4, h5, h6]
  ring

end FedAvg
end

/- Helpers from RunMoments. -/
section
/-!
Integrability bridges for Wang et al., *A Field Guide to Federated Optimization*,
Section 6.1.1, PDF p. 40, equations (11)--(14), and Appendix D, PDF pp. 86--88.
These are formal analytic bookkeeping for the stated stochastic model, not new
probabilistic assumptions. Mathlib's mean-value bound and L2 integrability API
supply the growth and moment estimates.
-/


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


/-- Client gradient evaluated at the current random state. -/
def clientGradient (R : Run P μ τ T η) (t k : ℕ) (i : Fin M) (ω : Ω) : ModelSpace d :=
  gradient (P.f i) (R.x t k i ω)

def clientNoise (R : Run P μ τ T η) (t k : ℕ) (i : Fin M) (ω : Ω) : ModelSpace d :=
  R.g t k i ω - clientGradient R t k i ω

def meanGradient (R : Run P μ τ T η) (t k : ℕ) (ω : Ω) : ModelSpace d :=
  (M : ℝ)⁻¹ • ∑ i, clientGradient R t k i ω

def meanNoise (R : Run P μ τ T η) (t k : ℕ) (ω : Ω) : ModelSpace d :=
  (M : ℝ)⁻¹ • ∑ i, clientNoise R t k i ω

def meanOracle (R : Run P μ τ T η) (t k : ℕ) (ω : Ω) : ModelSpace d :=
  (M : ℝ)⁻¹ • ∑ i, R.g t k i ω

lemma Run.gradient_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ)
    (i : Fin M) : MemLp (clientGradient R t k i) 2 μ := by
  exact (R.g_squareIntegrable t ht k hk i).condExp.ae_eq (R.unbiased t ht k hk i)

lemma Run.gradient_adapted (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ)
    (i : Fin M) : AEStronglyMeasurable[R.history (t * τ + k)] (clientGradient R t k i) μ := by
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr (R.unbiased t ht k hk i)

lemma Run.noise_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ)
    (i : Fin M) : MemLp (clientNoise R t k i) 2 μ :=
  (R.g_squareIntegrable t ht k hk i).sub (R.gradient_memLp ht hk i)

lemma Run.noise_condExp_zero (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ)
    (i : Fin M) : μ[clientNoise R t k i | R.history (t * τ + k)] =ᵐ[μ] 0 := by
  have hgrad := R.gradient_memLp ht hk i
  have hself := condExp_of_aestronglyMeasurable' (R.history.le _)
    (R.gradient_adapted ht hk i) (hgrad.integrable (by norm_num))
  have hsub := condExp_sub ((R.g_squareIntegrable t ht k hk i).integrable (by norm_num))
    (hgrad.integrable (by norm_num)) (R.history (t * τ + k))
  filter_upwards [hsub, hself, R.unbiased t ht k hk i] with ω hs hm hu
  change μ[clientNoise R t k i | R.history (t * τ + k)] ω = 0
  change μ[clientNoise R t k i | R.history (t * τ + k)] ω =
    μ[R.g t k i | R.history (t * τ + k)] ω -
    μ[clientGradient R t k i | R.history (t * τ + k)] ω at hs
  rw [hs, hm, hu]
  exact sub_self _

lemma Run.shadow_adapted (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k ≤ τ) :
    StronglyMeasurable[R.history (t * τ + k)] (shadow R t k) := by
  exact (Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun i _ ↦ R.x_adapted t ht k hk i)).const_smul (M : ℝ)⁻¹

lemma Run.meanGradient_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ) :
    MemLp (meanGradient R t k) 2 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ ↦ R.gradient_memLp ht hk i)).const_smul (M : ℝ)⁻¹

lemma Run.meanNoise_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ) :
    MemLp (meanNoise R t k) 2 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ ↦ R.noise_memLp ht hk i)).const_smul (M : ℝ)⁻¹

lemma Run.meanOracle_memLp (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ) :
    MemLp (meanOracle R t k) 2 μ := by
  exact (memLp_finsetSum Finset.univ
    (fun i _ ↦ R.g_squareIntegrable t ht k hk i)).const_smul (M : ℝ)⁻¹

lemma meanOracle_eq (R : Run P μ τ T η) (t k : ℕ) :
    meanOracle R t k = meanGradient R t k + meanNoise R t k := by
  funext ω
  simp only [meanOracle, meanGradient, meanNoise, clientNoise, Finset.sum_sub_distrib,
    smul_sub, Pi.add_apply]
  abel

lemma Run.shadow_update (R : Run P μ τ T η) {t k : ℕ} (ht : t < T) (hk : k < τ) :
    shadow R t (k + 1) =ᵐ[μ] fun ω ↦ shadow R t k ω - η • meanOracle R t k ω := by
  filter_upwards [Filter.eventually_all.mpr (R.local_update t ht k hk)] with ω hω
  simp only [shadow, meanOracle, hω, Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub]
  rw [smul_comm]


lemma Run.shadowDistanceSq_adapted (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k ≤ τ) :
    StronglyMeasurable[R.history (t * τ + k)] (shadowDistanceSq R t k) := by
  exact ((R.shadow_adapted ht hk).sub stronglyMeasurable_const).norm.pow 2

lemma Run.clientDriftSq_adapted (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k ≤ τ) (i : Fin M) :
    StronglyMeasurable[R.history (t * τ + k)] (clientDriftSq R t k i) := by
  exact ((R.x_adapted t ht k hk i).sub (R.shadow_adapted ht hk)).norm.pow 2

lemma Run.meanNoise_condExp_zero (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k < τ) :
    μ[meanNoise R t k | R.history (t * τ + k)] =ᵐ[μ] 0 := by
  have hs := condExp_finsetSum (s := Finset.univ)
    (fun i _ ↦ (R.noise_memLp ht hk i).integrable (by norm_num)) (R.history (t * τ + k))
  have hmul := condExp_smul (μ := μ) (M : ℝ)⁻¹
    (∑ i, clientNoise R t k i) (R.history (t * τ + k))
  have hz : ∀ᵐ ω ∂μ, ∀ i, μ[clientNoise R t k i | R.history (t * τ + k)] ω = 0 :=
    ae_all_iff.mpr (fun i ↦ R.noise_condExp_zero ht hk i)
  have hf : meanNoise R t k = (M : ℝ)⁻¹ • ∑ i, clientNoise R t k i := by
    funext ω
    simp [meanNoise]
  rw [hf]
  filter_upwards [hs, hmul, hz] with ω hs hm hz
  simp only [Pi.smul_apply] at hm
  rw [hm, hs]
  simp only [Finset.sum_apply, hz, Finset.sum_const_zero, smul_zero, Pi.zero_apply]

end FedAvg
end

/- Helpers from ConditionalVariance. -/
section
/-!
Conditional covariance cancellation for the stochastic oracle in Wang et al.,
*A Field Guide to Federated Optimization*, Appendix D.1, PDF p. 87, equation (27),
and the pairwise noise calculation in Appendix D.2, PDF pp. 87--88.

Mathlib supplies conditional-kernel product laws and unconditional bilinear
factorization; the bridge below specializes their composition to Euclidean vectors.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FedAvg

variable {d : ℕ} {Ω : Type*} {H : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f g : Ω → ModelSpace d}

theorem condIndepFun_ae_indep_kernel (hm : H ≤ mΩ)
    (hf : Measurable f) (hg : Measurable g) (hfg : CondIndepFun H hm f g μ) :
    ∀ᵐ ω ∂μ, IndepFun f g (condExpKernel μ H ω) := by
  have hmap := (condIndepFun_iff_map_prod_eq_prod_map_map hf hg).mp hfg
  filter_upwards [ae_of_ae_trim hm hmap] with ω hω
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
  simpa only [Kernel.map_apply _ (hf.prodMk hg), Kernel.prod_apply,
    Kernel.map_apply _ hf, Kernel.map_apply _ hg] using hω

theorem condExp_inner_of_condIndep (hm : H ≤ mΩ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (hfg : CondIndepFun H hm f g μ) :
    μ[fun ω ↦ inner ℝ (f ω) (g ω) | H] =ᵐ[μ]
      fun ω ↦ inner ℝ (μ[f | H] ω) (μ[g | H] ω) := by
  have hfi : Integrable f μ := hf2.integrable (by norm_num)
  have hgi : Integrable g μ := hg2.integrable (by norm_num)
  filter_upwards [condExp_ae_eq_integral_condExpKernel hm
      (inner_integrable_of_memLp hf2 hg2),
    condExp_ae_eq_integral_condExpKernel hm hfi,
    condExp_ae_eq_integral_condExpKernel hm hgi,
    hfi.condExpKernel_ae (m := H), hgi.condExpKernel_ae (m := H),
    condIndepFun_ae_indep_kernel hm hf hg hfg] with ω hinner hleft hright hfiω hgiω hind
  rw [hinner, hleft, hright]
  simpa only [innerSL_apply_apply] using hind.integral_bilin (𝕜 := ℝ) hfiω hgiω (innerSL ℝ)

omit [StandardBorelSpace Ω] in
theorem condExp_sub_condExp (hm : H ≤ mΩ) (hf : Integrable f μ) :
    μ[fun ω ↦ f ω - μ[f | H] ω | H] =ᵐ[μ] 0 := by
  have h := condExp_sub hf (integrable_condExp (f := f) (m := H)) H
  rw [condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp] at h
  simpa only [Pi.sub_apply, sub_self] using h

theorem condExp_inner_centered_of_condIndep (hm : H ≤ mΩ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (hfg : CondIndepFun H hm f g μ) :
    μ[fun ω ↦ inner ℝ (f ω - μ[f | H] ω) (g ω - μ[g | H] ω) | H] =ᵐ[μ] 0 := by
  have hgsub : MemLp (fun ω ↦ g ω - μ[g | H] ω) 2 μ := hg2.sub hg2.condExp
  have hfg0 := condExp_inner_of_condIndep hm hf hg hf2 hg2 hfg
  have hright := condExp_bilin_of_stronglyMeasurable_right (innerSL ℝ)
    (stronglyMeasurable_condExp (f := g) (m := H))
    (inner_integrable_of_memLp hf2 hg2.condExp) (hf2.integrable (by norm_num))
  have hleft := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ)
    (stronglyMeasurable_condExp (f := f) (m := H))
    (inner_integrable_of_memLp hf2.condExp hgsub) (hgsub.integrable (by norm_num))
  have hg0 := condExp_sub_condExp hm (hg2.integrable (by norm_num))
  have hsub₁ := condExp_sub (inner_integrable_of_memLp hf2 hg2)
    (inner_integrable_of_memLp hf2 (hg2.condExp (m := H))) H
  have hsub₂ := condExp_sub (inner_integrable_of_memLp hf2 hgsub)
    (inner_integrable_of_memLp (hf2.condExp (m := H)) hgsub) H
  simp only [Pi.sub_def, ← inner_sub_right] at hsub₁
  simp only [Pi.sub_def, ← inner_sub_left] at hsub₂
  filter_upwards [hfg0, hright, hleft, hg0, hsub₁, hsub₂] with ω hfgω hr hl hgω h1 h2
  change μ[fun ω ↦ inner ℝ (f ω) (μ[g | H] ω) | H] ω =
    inner ℝ (μ[f | H] ω) (μ[g | H] ω) at hr
  change μ[fun ω ↦ inner ℝ (μ[f | H] ω) (g ω - μ[g | H] ω) | H] ω =
    inner ℝ (μ[f | H] ω) (μ[fun ω ↦ g ω - μ[g | H] ω | H] ω) at hl
  simp only [Pi.zero_apply] at hgω
  simp only [h2, h1, hfgω, hr, hl, hgω, inner_zero_right, sub_self,
    Pi.zero_apply]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
theorem condExp_norm_sq_sub_of_orthogonal (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hfg : μ[fun ω ↦ inner ℝ (f ω) (g ω) | H] =ᵐ[μ] 0) :
    μ[fun ω ↦ ‖f ω - g ω‖ ^ 2 | H] =ᵐ[μ]
      fun ω ↦ μ[fun ω ↦ ‖f ω‖ ^ 2 | H] ω + μ[fun ω ↦ ‖g ω‖ ^ 2 | H] ω := by
  have hf := hf2.norm.integrable_sq
  have hg := hg2.norm.integrable_sq
  have hfgI := inner_integrable_of_memLp hf2 hg2
  have hsub := condExp_sub hf (hfgI.const_mul 2) H
  have hadd := condExp_add (hf.sub (hfgI.const_mul 2)) hg H
  have hmul := condExp_smul (μ := μ) (2 : ℝ) (fun ω ↦ inner ℝ (f ω) (g ω)) H
  simp_rw [norm_sub_sq_real]
  filter_upwards [hsub, hadd, hmul, hfg] with ω hs ha hm hz
  simp only [Pi.add_def, Pi.sub_def, Pi.smul_def, smul_eq_mul, Pi.zero_apply] at hs ha hm hz
  rw [ha, hs, hm, hz]
  ring

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
theorem condExp_norm_sq_sum_of_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : ι → Ω → ModelSpace d) (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hcross : ∀ i j, i ≠ j → μ[fun ω ↦ inner ℝ (Z i ω) (Z j ω) | H] =ᵐ[μ] 0) :
    μ[fun ω ↦ ‖∑ i, Z i ω‖ ^ 2 | H] =ᵐ[μ]
      fun ω ↦ ∑ i, μ[fun ω ↦ ‖Z i ω‖ ^ 2 | H] ω := by
  have hI (i j : ι) : Integrable (fun ω ↦ inner ℝ (Z i ω) (Z j ω)) μ :=
    inner_integrable_of_memLp (hZ i) (hZ j)
  have hexp : (fun ω ↦ ‖∑ i, Z i ω‖ ^ 2) =
      ∑ i, ∑ j, fun ω ↦ inner ℝ (Z i ω) (Z j ω) := by
    funext ω
    simp only [Finset.sum_apply, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
    exact Finset.sum_comm
  have hsum := condExp_finsetSum (s := Finset.univ)
    (fun i _ ↦ integrable_finsetSum' Finset.univ (fun j _ ↦ hI i j)) H
  have hrow (i : ι) := condExp_finsetSum (s := Finset.univ) (fun j _ ↦ hI i j) H
  have hentry (i j : ι) : μ[fun ω ↦ inner ℝ (Z i ω) (Z j ω) | H] =ᵐ[μ]
      fun ω ↦ if i = j then μ[fun ω ↦ ‖Z i ω‖ ^ 2 | H] ω else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_true, real_inner_self_eq_norm_sq]
      exact Filter.EventuallyEq.rfl
    · simpa only [hij, if_false] using hcross i j hij
  rw [hexp]
  filter_upwards [hsum, Filter.eventually_all.mpr hrow,
    Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr (hentry i))] with ω hs hr he
  simp only [Finset.sum_apply] at hs hr
  rw [hs]
  simp only [hr, he, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
theorem condExp_norm_sq_mean_le {M : ℕ} (hM : 0 < M)
    (Z : Fin M → Ω → ModelSpace d) (hZ : ∀ i, MemLp (Z i) 2 μ) (σ : ℝ)
    (hcross : ∀ i j, i ≠ j → μ[fun ω ↦ inner ℝ (Z i ω) (Z j ω) | H] =ᵐ[μ] 0)
    (hvar : ∀ i, μ[fun ω ↦ ‖Z i ω‖ ^ 2 | H] ≤ᵐ[μ] fun _ ↦ σ ^ 2) :
    μ[fun ω ↦ ‖(M : ℝ)⁻¹ • ∑ i, Z i ω‖ ^ 2 | H] ≤ᵐ[μ]
      fun _ ↦ σ ^ 2 / M := by
  have hsum := condExp_norm_sq_sum_of_orthogonal Z hZ hcross
  have hscale := condExp_smul (μ := μ) ((M : ℝ)⁻¹ ^ 2)
    (fun ω ↦ ‖∑ i, Z i ω‖ ^ 2) H
  have hexp : (fun ω ↦ ‖(M : ℝ)⁻¹ • ∑ i, Z i ω‖ ^ 2) =
      ((M : ℝ)⁻¹ ^ 2) • (fun ω ↦ ‖∑ i, Z i ω‖ ^ 2) := by
    funext ω
    simp only [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, smul_eq_mul]
  rw [hexp]
  filter_upwards [hsum, hscale, Filter.eventually_all.mpr hvar] with ω hs hc hv
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  rw [hc, hs]
  calc
    (M : ℝ)⁻¹ ^ 2 * ∑ i, μ[fun ω ↦ ‖Z i ω‖ ^ 2 | H] ω
        ≤ (M : ℝ)⁻¹ ^ 2 * ∑ _i : Fin M, σ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hv i)) (sq_nonneg _)
    _ = σ ^ 2 / M := by
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

variable {M τ T : ℕ} {η : ℝ} {P : Problem d M}

theorem Run.noise_inner_condExp_zero (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k < τ) {i j : Fin M} (hij : i ≠ j) :
    μ[fun ω ↦ inner ℝ (clientNoise R t k i ω) (clientNoise R t k j ω) |
      R.history (t * τ + k)] =ᵐ[μ] 0 := by
  have hc := condExp_inner_centered_of_condIndep (R.history.le (t * τ + k))
    ((R.g_adapted t ht k hk i).mono (R.history.le _)).measurable
    ((R.g_adapted t ht k hk j).mono (R.history.le _)).measurable
    (R.g_squareIntegrable t ht k hk i) (R.g_squareIntegrable t ht k hk j)
    ((R.independent t ht k hk).condIndepFun hij)
  have heq : (fun ω ↦ inner ℝ (clientNoise R t k i ω) (clientNoise R t k j ω)) =ᵐ[μ]
      fun ω ↦ inner ℝ
        (R.g t k i ω - μ[R.g t k i | R.history (t * τ + k)] ω)
        (R.g t k j ω - μ[R.g t k j | R.history (t * τ + k)] ω) := by
    filter_upwards [R.unbiased t ht k hk i, R.unbiased t ht k hk j] with ω hi hj
    simp only [clientNoise, clientGradient, hi, hj]
  exact (condExp_congr_ae heq).trans hc

theorem Run.pairNoise_variance (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k < τ) (i j : Fin M) :
    μ[fun ω ↦ ‖clientNoise R t k i ω - clientNoise R t k j ω‖ ^ 2 |
      R.history (t * τ + k)] ≤ᵐ[μ] fun _ ↦ 2 * P.σ ^ 2 := by
  by_cases hij : i = j
  · subst j
    filter_upwards [] with ω
    simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    rw [condExp_const (R.history.le _)]
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  · have hc := condExp_norm_sq_sub_of_orthogonal (R.noise_memLp ht hk i)
      (R.noise_memLp ht hk j) (R.noise_inner_condExp_zero ht hk hij)
    filter_upwards [hc, R.variance t ht k hk i, R.variance t ht k hk j] with ω hc hi hj
    rw [hc]
    change μ[fun ω ↦ ‖clientNoise R t k i ω‖ ^ 2 | R.history (t * τ + k)] ω ≤ P.σ ^ 2 at hi
    change μ[fun ω ↦ ‖clientNoise R t k j ω‖ ^ 2 | R.history (t * τ + k)] ω ≤ P.σ ^ 2 at hj
    linarith

theorem Run.meanNoise_variance (R : Run P μ τ T η) {t k : ℕ}
    (ht : t < T) (hk : k < τ) :
    μ[fun ω ↦ ‖meanNoise R t k ω‖ ^ 2 | R.history (t * τ + k)] ≤ᵐ[μ]
      fun _ ↦ P.σ ^ 2 / M := by
  exact condExp_norm_sq_mean_le P.clients_pos (clientNoise R t k)
    (R.noise_memLp ht hk) P.σ (fun _ _ hij ↦ R.noise_inner_condExp_zero ht hk hij)
    (R.variance t ht k hk)

end FedAvg
end

/- Helpers from ProgressDeterministic. -/
section
open scoped BigOperators InnerProductSpace

namespace FedAvg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_add_sq_le_twice (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hp := norm_add_sq_real u v
  have hm := norm_sub_sq_real u v
  nlinarith [sq_nonneg ‖u-v‖]

variable {d M : ℕ} (P : Problem d M)

/-- Averaging the smoothness and convexity bounds in Appendix D.1, equation (25). -/
theorem objective_gap_local_gradients (xs : Fin M → ModelSpace d)
    (X Y z : ModelSpace d) :
    objective P.f Y - objective P.f z ≤
      ⟪(M : ℝ)⁻¹ • ∑ i, gradient (P.f i) (xs i), Y-z⟫_ℝ +
      P.L * ‖Y-X‖ ^ 2 + (P.L / M) * ∑ i, ‖xs i-X‖ ^ 2 := by
  have hi (i : Fin M) :
      P.f i Y - P.f i z ≤ ⟪gradient (P.f i) (xs i), Y-z⟫_ℝ +
        P.L * ‖Y-X‖ ^ 2 + P.L * ‖xs i-X‖ ^ 2 := by
    have hdes := smooth_descent (P.hasGradient i) P.smoothness_pos.le (P.smooth i) (xs i) Y
    have hlo := convex_gradient_lower (P.hasGradient i) (P.convex i) (xs i) z
    have hn := norm_add_sq_le_twice (Y-X) (X-xs i)
    rw [show Y-X + (X-xs i) = Y-xs i by abel, norm_sub_rev X (xs i)] at hn
    have heq : ⟪gradient (P.f i) (xs i), Y-z⟫_ℝ =
        ⟪gradient (P.f i) (xs i), Y-xs i⟫_ℝ -
          ⟪gradient (P.f i) (xs i), z-xs i⟫_ℝ := by
      rw [← inner_sub_right]
      congr 1
      abel
    nlinarith [P.smoothness_pos]
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i))
    (inv_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ) ≤ M))
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.clients_pos)
  simpa only [objective, Finset.sum_sub_distrib, mul_sub, real_inner_smul_left,
    sum_inner, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hM, one_mul, div_eq_mul_inv, mul_comm P.L (M : ℝ)⁻¹] using hsum

theorem potential_step_identity (X G z : E) {η : ℝ} (hη : 0 < η) :
    ⟪G, X - η • G - z⟫_ℝ =
      (‖X-z‖ ^ 2 - ‖X-η • G-z‖ ^ 2) / (2*η) -
        ‖(X-η • G)-X‖ ^ 2 / (2*η) := by
  have hn := norm_sub_sq_real (X-z) (η • G)
  rw [inner_smul_right, real_inner_comm G (X-z), norm_smul, Real.norm_eq_abs,
    abs_of_pos hη] at hn
  have hvec : X-η • G-z = (X-z)-η • G := by abel
  have hstep : X-η • G-X = -(η • G) := by abel
  rw [hvec, hstep, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  field_simp
  nlinarith

theorem noise_inner_young (N s : E) {η : ℝ} (hη : 0 < η) :
    -⟪N,s⟫_ℝ ≤ η * ‖N‖ ^ 2 + ‖s‖ ^ 2 / (4*η) := by
  have hn := norm_add_sq_real ((2*η) • N) s
  rw [real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2*η)] at hn
  have hp := sq_nonneg ‖(2*η) • N+s‖
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 4*η)).mp
  have heq : (η * ‖N‖ ^ 2 + ‖s‖ ^ 2 / (4*η)) * (4*η) =
      4*η^2*‖N‖^2+‖s‖^2 := by field_simp
  rw [heq]
  nlinarith

/-- Pointwise progress estimate behind Appendix D.1, equations (24)--(27). -/
theorem progress_one_step (xs gs : Fin M → ModelSpace d) {η : ℝ}
    (hη : 0 < η) (hηL : η ≤ 1 / (4 * P.L)) :
    let X := (M : ℝ)⁻¹ • ∑ i, xs i
    let G := (M : ℝ)⁻¹ • ∑ i, gs i
    let A := (M : ℝ)⁻¹ • ∑ i, gradient (P.f i) (xs i)
    let N := G-A
    let Y := X-η • G
    objective P.f Y - objective P.f P.xstar ≤
      (‖X-P.xstar‖ ^ 2 - ‖Y-P.xstar‖ ^ 2) / (2*η) + η * ‖N‖ ^ 2 +
        (P.L / M) * ∑ i, ‖xs i-X‖ ^ 2 - ⟪N, X-P.xstar⟫_ℝ := by
  dsimp only
  let X := (M : ℝ)⁻¹ • ∑ i, xs i
  let G := (M : ℝ)⁻¹ • ∑ i, gs i
  let A := (M : ℝ)⁻¹ • ∑ i, gradient (P.f i) (xs i)
  let N := G-A
  let Y := X-η • G
  change objective P.f Y - objective P.f P.xstar ≤
    (‖X-P.xstar‖ ^ 2 - ‖Y-P.xstar‖ ^ 2) / (2*η) + η * ‖N‖ ^ 2 +
      (P.L / M) * ∑ i, ‖xs i-X‖ ^ 2 - ⟪N, X-P.xstar⟫_ℝ
  have hgap := objective_gap_local_gradients P xs X Y P.xstar
  change objective P.f Y - objective P.f P.xstar ≤
    ⟪A,Y-P.xstar⟫_ℝ + P.L * ‖Y-X‖ ^ 2 + (P.L/M) * ∑ i, ‖xs i-X‖ ^ 2 at hgap
  have hpot := potential_step_identity X G P.xstar hη
  change ⟪G,Y-P.xstar⟫_ℝ =
    (‖X-P.xstar‖ ^ 2 - ‖Y-P.xstar‖ ^ 2) / (2*η) - ‖Y-X‖ ^ 2 / (2*η) at hpot
  have hnoise := noise_inner_young N (Y-X) hη
  have hinn : ⟪A,Y-P.xstar⟫_ℝ = ⟪G,Y-P.xstar⟫_ℝ -
      ⟪N,X-P.xstar⟫_ℝ - ⟪N,Y-X⟫_ℝ := by
    have hv : Y-P.xstar = (X-P.xstar)+(Y-X) := by abel
    dsimp [N]
    simp only [inner_sub_left, hv, inner_add_right]
    ring
  have hLη : P.L ≤ 1/(4*η) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*η)).mpr
    have hh := (le_div_iff₀ (mul_pos (by norm_num) P.smoothness_pos)).mp hηL
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_right hLη (sq_nonneg ‖Y-X‖)
  have hhalf : ‖Y-X‖ ^ 2 / (2*η) = 2 * (‖Y-X‖ ^ 2 / (4*η)) := by ring
  rw [one_div_mul_eq_div] at hsmall
  linarith

end FedAvg
end

/- Helpers from ProgressConditional. -/
section
/-! Conditional one-step progress, Wang et al., arXiv:2107.06917v1,
Appendix D.1, PDF pp. 86–87, equations (24)–(27). -/

open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace FedAvg

variable {Ω : Type*} {H : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private lemma condExp_step_affine {a b v d z : Ω → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hv : Integrable v μ)
    (hd : Integrable d μ) (hz : Integrable z μ) (c η : ℝ) :
    μ[fun ω ↦ (a ω-b ω)/c + η*v ω+d ω-z ω | H] =ᵐ[μ]
      fun ω ↦ (μ[a|H] ω-μ[b|H] ω)/c + η*μ[v|H] ω+μ[d|H] ω-μ[z|H] ω := by
  have h1 := condExp_sub ha hb H
  have h2 := condExp_smul (μ := μ) c⁻¹ (fun ω ↦ a ω-b ω) H
  have h3 := condExp_smul (μ := μ) η v H
  have h4 := condExp_add ((ha.sub hb).const_mul c⁻¹) (hv.const_mul η) H
  have h5 := condExp_add (((ha.sub hb).const_mul c⁻¹).add (hv.const_mul η)) hd H
  have h6 := condExp_sub ((((ha.sub hb).const_mul c⁻¹).add (hv.const_mul η)).add hd) hz H
  have heq : (fun ω ↦ (a ω-b ω)/c + η*v ω+d ω-z ω) =
      fun ω ↦ (c⁻¹*(a ω-b ω) + η*v ω)+d ω-z ω := by
    funext ω
    ring
  rw [heq]
  filter_upwards [h1,h2,h3,h4,h5,h6] with ω h1 h2 h3 h4 h5 h6
  simp only [Pi.sub_def, Pi.add_def, Pi.smul_def, smul_eq_mul] at h1 h2 h3 h4 h5 h6
  rw [h6,h5,h4,h2,h3,h1]
  ring

variable [StandardBorelSpace Ω] {d M τ T : ℕ} {η : ℝ} {P : Problem d M}

theorem Run.conditional_progress_step (R : Run P μ τ T η)
    (hη : 0 < η) (hηL : η ≤ 1 / (4 * P.L)) {t k : ℕ}
    (ht : t < T) (hk : k < τ) :
    μ[fun ω ↦ objective P.f (shadow R t (k+1) ω)-objective P.f P.xstar |
      R.history (t*τ+k)] ≤ᵐ[μ]
    fun ω ↦ (shadowDistanceSq R t k ω -
      μ[shadowDistanceSq R t (k+1) | R.history (t*τ+k)] ω)/(2*η) +
      η*P.σ^2/M + (P.L/M)*∑ i, clientDriftSq R t k i ω := by
  have hk0 := Nat.le_of_lt hk
  have hk1 := Nat.succ_le_of_lt hk
  let D : Ω → ℝ := fun ω ↦ (P.L/M)*∑ i, clientDriftSq R t k i ω
  let V : Ω → ℝ := fun ω ↦ ‖meanNoise R t k ω‖^2
  let Z : Ω → ℝ := fun ω ↦ ⟪shadow R t k ω-P.xstar, meanNoise R t k ω⟫_ℝ
  have hA := shadowDistanceSq_integrable R ht hk0
  have hB := shadowDistanceSq_integrable R ht hk1
  have hV : Integrable V μ := (R.meanNoise_memLp ht hk).norm.integrable_sq
  have hD : Integrable D μ := by
    simpa only [D, Finset.sum_apply] using
      (integrable_finsetSum' Finset.univ (fun i _ ↦ clientDriftSq_integrable R ht hk0 i)).const_mul (P.L/M)
  have hXm := (R.shadow_adapted ht hk0).sub (stronglyMeasurable_const (b := P.xstar))
  have hX2 := (shadow_memLp R ht hk0).sub (memLp_const P.xstar)
  have hZ : Integrable Z μ := inner_integrable_of_memLp hX2 (R.meanNoise_memLp ht hk)
  have hZ0 : μ[Z | R.history (t*τ+k)] =ᵐ[μ] 0 :=
    condExp_inner_zero hX2 (R.meanNoise_memLp ht hk) hXm.aestronglyMeasurable
      (R.meanNoise_condExp_zero ht hk)
  have hDsm : StronglyMeasurable[R.history (t*τ+k)] D :=
    (Finset.stronglyMeasurable_fun_sum Finset.univ
      (fun i _ ↦ R.clientDriftSq_adapted ht hk0 i)).const_mul (P.L/M)
  have hAself := condExp_of_stronglyMeasurable (R.history.le _)
    (R.shadowDistanceSq_adapted ht hk0) hA
  have hDself := condExp_of_stronglyMeasurable (R.history.le _) hDsm hD
  have hpoint : (fun ω ↦ objective P.f (shadow R t (k+1) ω)-objective P.f P.xstar) ≤ᵐ[μ]
      fun ω ↦ (shadowDistanceSq R t k ω-shadowDistanceSq R t (k+1) ω)/(2*η) +
        η*V ω + D ω - Z ω := by
    filter_upwards [R.shadow_update ht hk] with ω hu
    have hp := progress_one_step P (fun i ↦ R.x t k i ω) (fun i ↦ R.g t k i ω) hη hηL
    have hn : (M:ℝ)⁻¹ • ∑ i, R.g t k i ω -
        (M:ℝ)⁻¹ • ∑ i, gradient (P.f i) (R.x t k i ω) = meanNoise R t k ω := by
      change meanOracle R t k ω-meanGradient R t k ω=meanNoise R t k ω
      rw [meanOracle_eq]
      simp only [Pi.add_apply, add_sub_cancel_left]
    change objective P.f (shadow R t k ω-η • meanOracle R t k ω)-objective P.f P.xstar ≤
      (‖shadow R t k ω-P.xstar‖^2 - ‖shadow R t k ω-η • meanOracle R t k ω-P.xstar‖^2)/(2*η) +
      η*‖(M:ℝ)⁻¹ • ∑ i, R.g t k i ω -
        (M:ℝ)⁻¹ • ∑ i, gradient (P.f i) (R.x t k i ω)‖^2 + D ω -
        ⟪(M:ℝ)⁻¹ • ∑ i, R.g t k i ω -
        (M:ℝ)⁻¹ • ∑ i, gradient (P.f i) (R.x t k i ω), shadow R t k ω-P.xstar⟫_ℝ at hp
    rw [hn, ← hu, real_inner_comm] at hp
    exact hp
  have hmono := condExp_mono (m := R.history (t*τ+k))
    ((objective_integrable_comp P (shadow_memLp R ht hk1)).sub (integrable_const _))
    (((hA.sub hB).div_const (2*η)).add (hV.const_mul η) |>.add hD |>.sub hZ) hpoint
  have hlin := condExp_step_affine (H := R.history (t*τ+k)) hA hB hV hD hZ (2*η) η
  rw [hAself, hDself] at hlin
  filter_upwards [hmono, hlin, hZ0, R.meanNoise_variance ht hk]
    with ω hm hl hz hv
  simp only [Pi.zero_apply] at hz
  simp only [Pi.sub_def, Pi.add_def] at hm
  rw [hl,hz,sub_zero] at hm
  calc
    _ ≤ _ := hm
    _ ≤ _ := by
      dsimp only [D]
      have hv' := mul_le_mul_of_nonneg_left hv hη.le
      change η*μ[V | R.history (t*τ+k)] ω ≤ η*(P.σ^2/M) at hv'
      rw [← mul_div_assoc] at hv'
      exact add_le_add (add_le_add le_rfl hv') le_rfl

end FedAvg
end

/- Helpers from ProgressTelescoping. -/
section
open MeasureTheory
open scoped BigOperators

namespace FedAvg

variable {d M : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem d M} {τ T : ℕ} {η : ℝ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
theorem condExp_real_const_mul (c : ℝ) (f : Ω → ℝ) (H : MeasurableSpace Ω) :
    μ[(fun ω ↦ c * f ω) | H] =ᵐ[μ] fun ω ↦ c * μ[f | H] ω := by
  exact condExp_smul (μ := μ) c f H

omit [StandardBorelSpace Ω] in
theorem condExp_progress_affine {f g : Ω → ℝ} {h : Fin M → Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : ∀ i, Integrable (h i) μ)
    (a b c : ℝ) {H : MeasurableSpace Ω} (hH : H ≤ mΩ) :
    μ[(fun ω ↦ (f ω-g ω)/a+c+b*∑ i, h i ω) | H] =ᵐ[μ]
      fun ω ↦ (μ[f|H] ω-μ[g|H] ω)/a+c+b*∑ i, μ[h i|H] ω := by
  have hi1 : Integrable (fun ω ↦ (f ω-g ω)/a) μ := (hf.sub hg).div_const a
  have hi2 : Integrable (fun ω ↦ b*∑ i, h i ω) μ :=
    (integrable_finsetSum Finset.univ (fun i _ ↦ hh i)).const_mul b
  have h1 := condExp_add (hi1.add (integrable_const c)) hi2 H
  have h2 := condExp_add hi1 (integrable_const c) H
  have h3 := condExp_real_const_mul (mΩ := mΩ) (μ := μ) a⁻¹ (fun ω ↦ f ω-g ω) H
  have h4 := condExp_sub hf hg H
  have h5 := condExp_real_const_mul (mΩ := mΩ) (μ := μ) b (fun ω ↦ ∑ i, h i ω) H
  have h6 := condExp_finsetSum (fun i (_ : i ∈ Finset.univ) ↦ hh i) H
  have heq : (∑ i, h i) = fun ω ↦ ∑ i, h i ω := by funext ω; simp
  rw [heq] at h6
  filter_upwards [h1, h2, h3, h4, h5, h6] with ω h1 h2 h3 h4 h5 h6
  simp only [Pi.add_def, Pi.sub_def, Finset.sum_apply] at h1 h2 h4 h6
  simp only [div_eq_inv_mul] at h1 h2 ⊢
  rw [h1, h2, h3, h4, h5, h6, condExp_const hH c]

/-- Conditioning each local progress bound on the start of its round and telescoping. -/
theorem perRoundProgress_of_step (R : Run P μ τ T η) {t : ℕ}
    (ht : t < T) (hτ : 0 < τ) (hη : 0 < η)
    (hstep : ∀ k, k < τ →
      μ[(fun ω ↦ objective P.f (shadow R t (k+1) ω)-objective P.f P.xstar) |
        R.history (t*τ+k)] ≤ᵐ[μ] fun ω ↦
          (shadowDistanceSq R t k ω -
            μ[shadowDistanceSq R t (k+1) | R.history (t*τ+k)] ω)/(2*η) +
            η*P.σ^2/M+(P.L/M)*∑ i, clientDriftSq R t k i ω) :
    μ[roundLoss R t | R.history (t*τ)] ≤ᵐ[μ] progressRHS R t := by
  let loss : ℕ → Ω → ℝ := fun k ω ↦
    objective P.f (shadow R t (k+1) ω)-objective P.f P.xstar
  have hloss (k : ℕ) (hk : k < τ) : Integrable (loss k) μ :=
    (objective_integrable_comp P (shadow_memLp R ht (Nat.succ_le_of_lt hk))).sub
      (integrable_const _)
  have hb (k : ℕ) (hk : k < τ) :
      μ[loss k | R.history (t*τ)] ≤ᵐ[μ] fun ω ↦
        (μ[shadowDistanceSq R t k | R.history (t*τ)] ω -
          μ[shadowDistanceSq R t (k+1) | R.history (t*τ)] ω)/(2*η) +
          η*P.σ^2/M+(P.L/M)*∑ i,
            μ[clientDriftSq R t k i | R.history (t*τ)] ω := by
    have hd := shadowDistanceSq_integrable R ht hk.le
    have hc (i : Fin M) := clientDriftSq_integrable R ht hk.le i
    have hrhs : Integrable (fun ω ↦
        (shadowDistanceSq R t k ω -
          μ[shadowDistanceSq R t (k+1) | R.history (t*τ+k)] ω)/(2*η) +
          η*P.σ^2/M+(P.L/M)*∑ i, clientDriftSq R t k i ω) μ :=
      (((hd.sub integrable_condExp).div_const _).add (integrable_const _)).add
        ((integrable_finsetSum Finset.univ (fun i _ ↦ hc i)).const_mul _)
    have hm := condExp_mono (m := R.history (t*τ)) integrable_condExp hrhs (hstep k hk)
    have hle : R.history (t*τ) ≤ R.history (t*τ+k) := R.history.mono (Nat.le_add_right _ _)
    have hl := condExp_condExp_of_le (μ := μ) (f := loss k) hle (R.history.le _)
    have hdnext := condExp_condExp_of_le (μ := μ) (f := shadowDistanceSq R t (k+1))
      hle (R.history.le _)
    have ha := condExp_progress_affine
      (g := μ[shadowDistanceSq R t (k+1) | R.history (t*τ+k)]) hd integrable_condExp hc
      (2*η) (P.L/M) (η*P.σ^2/M) (R.history.le (t*τ))
    filter_upwards [hm, hl, hdnext, ha] with ω hm hl hdnext ha
    change μ[μ[loss k | R.history (t*τ+k)] | R.history (t*τ)] ω ≤ _ at hm
    rw [hl, ha, hdnext] at hm
    exact hm
  have hsum := condExp_finsetSum (s := Finset.range τ)
    (fun k hk ↦ hloss k (Finset.mem_range.mp hk)) (R.history (t*τ))
  have heqsum : (∑ k ∈ Finset.range τ, loss k) =
      fun ω ↦ ∑ k ∈ Finset.range τ, loss k ω := by funext ω; simp
  rw [heqsum] at hsum
  have hmul := condExp_real_const_mul (μ := μ) (τ : ℝ)⁻¹
    (fun ω ↦ ∑ k ∈ Finset.range τ, loss k ω) (R.history (t*τ))
  have hself : μ[shadowDistanceSq R t 0 | R.history (t*τ)] = shadowDistanceSq R t 0 := by
    apply condExp_of_stronglyMeasurable (R.history.le _)
    · simpa only [Nat.add_zero] using R.shadowDistanceSq_adapted ht (Nat.zero_le τ)
    · exact shadowDistanceSq_integrable R ht (Nat.zero_le τ)
  filter_upwards [hmul, hsum,
    (Filter.eventually_all_finset (Finset.range τ)).mpr
      (fun k hk ↦ hb k (Finset.mem_range.mp hk))] with ω hmul hsum hb
  change μ[roundLoss R t | R.history (t*τ)] ω =
    (τ : ℝ)⁻¹ * μ[(fun ω ↦ ∑ k ∈ Finset.range τ, loss k ω) | R.history (t*τ)] ω at hmul
  simp only [Finset.sum_apply] at hsum
  rw [hmul, hsum]
  have hs := Finset.sum_le_sum (s := Finset.range τ) (fun k hk ↦ hb k hk)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub',
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs
    (inv_nonneg.mpr (Nat.cast_nonneg τ : (0:ℝ) ≤ τ))
  refine hscaled.trans_eq ?_
  rw [hself, Finset.sum_comm]
  dsimp only [progressRHS, progressTerm, deviationTerm]
  have hτ0 : (τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hτ)
  field_simp
  ring

end FedAvg
end

open MeasureTheory FedAvg
universe u

theorem solution :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ T : ℕ) (η : ℝ),
    0 < τ → 0 < T → 0 < η → η ≤ 1 / (4 * P.L) →
    ∀ (R : Run P μ τ T η) (t : ℕ), t < T →
      μ[roundLoss R t | R.history (t * τ)] ≤ᵐ[μ] progressRHS R t := by
  intro d M P Ω _ _ μ _ τ T η hτ _hT hη hηL R t ht
  exact perRoundProgress_of_step R ht hτ hη
    (fun k hk ↦ R.conditional_progress_step hη hηL ht hk)
