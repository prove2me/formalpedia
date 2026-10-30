-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:28:13.550013+00:00
-- url     : https://prove2.me/submissions/7a1a213b-55bf-4897-b0c2-847afb4c5023

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_QVTelescope
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: Tanaka telescoping ⟹ window occupation lower bound

Telescoping the single-step `|D|`-drift (brick 85) over the evolving distribution `distPow K μ₀ t`
(the law of the walk after `t` steps) yields, for a mean-preserving bounded-increment kernel,

  `E|D_T| − E|D_0| ≤ b · ∑_{t<T} (window-occupation at step t)`,

i.e. `window-occupation ≥ (E|D_T| − E|D_0|)/b`.  Combined with the Paley–Zygmund bound `E|D_T| ≥ c√T`
(brick 84) and the per-step second/fourth moments of the Erdős rank-difference walk, this gives the
occupation lower bound `≥ 1/δ` that closes the Hardy–Ramanujan convergence.  All deterministic finite-sum
algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

lemma distPow_nonneg (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKnn : ∀ x z, 0 ≤ K x z)
    (hμ0 : ∀ x, 0 ≤ μ0 x) : ∀ t x, 0 ≤ distPow K μ0 t x := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih => exact fun z => Finset.sum_nonneg (fun x _ => mul_nonneg (ih x) (hKnn x z))

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: quadratic-variation telescoping (Doob decomposition for `D²`)

For a mean-preserving kernel, `D²` has Doob compensator equal to the cumulative local variance
`locVar x = ∑_z K x z (D z − D x)²`:

  `E[D_T²] − E[D_0²] = ∑_{t<T} ∑_x distPow t x · locVar x`.

With a uniform local-variance lower bound `v₀ ≤ locVar` this gives `E[D_T²] ≥ E[D_0²] + v₀·T`, the lower
quadratic-variation feeding the Paley–Zygmund bound `E|D_T| ≥ c√T`.  Deterministic finite-sum.
Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- For a mean-preserving step, the second-moment drift equals the local variance. -/
lemma locVar_eq (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) (hKsum : ∑ z, K x z = 1)
    (hmart : ∑ z, K x z * D z = D x) :
    locVar K D x = (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by
  unfold locVar
  have expand : ∀ z, K x z * (D z - D x) ^ 2
      = K x z * (D z) ^ 2 - (2 * D x) * (K x z * D z) + (D x) ^ 2 * K x z := by
    intro z; ring
  rw [Finset.sum_congr rfl (fun z _ => expand z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hmart, hKsum]
  ring

/-- The law `distPow` stays a probability distribution. -/
lemma distPow_sum (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0 : ∑ x, μ0 x = 1) : ∀ t, ∑ x, distPow K μ0 t x = 1 := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih =>
    simp only [distPow]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun x _ => by rw [← Finset.mul_sum, hKsum x, mul_one])]
    exact ih

/-- **Quadratic-variation telescoping (Doob for `D²`).** -/
theorem sq_moment_telescope (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ)
    (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 2) - (∑ x, μ0 x * (D x) ^ 2)
      = ∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 2)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * (D z) ^ 2) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * (D z) ^ 2)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * (D z) ^ 2 from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 2)
        - (∑ x, distPow K μ0 T x * (D x) ^ 2)
        = ∑ x, distPow K μ0 T x * locVar K D x := by
      rw [hswap, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← mul_sub, locVar_eq K D x (hKsum x) (hmart x)]
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: per-step fourth-moment drift bound

For a mean-preserving kernel with bounded increments `b`, the one-step fourth-moment drift is controlled
by the second moment:

  `∑_z K x z (D z)⁴ − (D x)⁴ ≤ 8 b² (D x)² + 3 b⁴`.

Telescoped (with the upper quadratic variation `E[D_t²] ≤ D₀² + b² t`) this gives the BDG-type bound
`E[D_T⁴] ≤ C b⁴ T²`, the fourth moment feeding the Paley–Zygmund anti-concentration `E|D_T| ≥ c√T`.
Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **Per-step fourth-moment drift bound.** -/
theorem fourth_drift_le (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b) (x : ι)
    (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1) (hmart : ∑ z, K x z * D z = D x)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * (D z) ^ 4) - (D x) ^ 4 ≤ 8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4 := by
  set lv := ∑ z, K x z * (D z - D x) ^ 2 with hlvdef
  set M3 := ∑ z, K x z * (D z - D x) ^ 3 with hM3def
  set M4 := ∑ z, K x z * (D z - D x) ^ 4 with hM4def
  -- mean-zero increment
  have hmean0 : (∑ z, K x z * (D z - D x)) = 0 := by
    have h : ∀ z, K x z * (D z - D x) = K x z * D z - D x * K x z := fun z => by ring
    rw [Finset.sum_congr rfl (fun z _ => h z), Finset.sum_sub_distrib, ← Finset.mul_sum, hmart, hKsum]
    ring
  -- binomial expansion of the fourth moment
  have hexp : (∑ z, K x z * (D z) ^ 4) = (D x) ^ 4 + 6 * (D x) ^ 2 * lv + 4 * (D x) * M3 + M4 := by
    have key : ∀ z, K x z * (D z) ^ 4
        = (D x) ^ 4 * K x z + 4 * (D x) ^ 3 * (K x z * (D z - D x))
          + 6 * (D x) ^ 2 * (K x z * (D z - D x) ^ 2)
          + 4 * (D x) * (K x z * (D z - D x) ^ 3) + K x z * (D z - D x) ^ 4 := fun z => by ring
    rw [Finset.sum_congr rfl (fun z _ => key z)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hKsum, hmean0,
      hlvdef, hM3def, hM4def]
    ring
  -- moment bounds from the increment bound b
  have hlv_le : lv ≤ b ^ 2 := by
    rw [hlvdef]
    calc ∑ z, K x z * (D z - D x) ^ 2 ≤ ∑ z, K x z * b ^ 2 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hz : K x z = 0
          · rw [hz, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
            have := hbinc z hz
            nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), this]
      _ = b ^ 2 := by rw [← Finset.sum_mul, hKsum, one_mul]
  have hlv_nn : 0 ≤ lv := by
    rw [hlvdef]; exact Finset.sum_nonneg (fun z _ => mul_nonneg (hKnn z) (sq_nonneg _))
  have hM4_le : M4 ≤ b ^ 2 * lv := by
    rw [hM4def, hlvdef, Finset.mul_sum]
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz : K x z = 0
    · rw [hz, zero_mul]; positivity
    · have hb := hbinc z hz
      have hsq : (D z - D x) ^ 2 ≤ b ^ 2 := by nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), hb]
      have h4 : (D z - D x) ^ 4 ≤ b ^ 2 * (D z - D x) ^ 2 := by nlinarith [sq_nonneg (D z - D x), hsq]
      calc K x z * (D z - D x) ^ 4 ≤ K x z * (b ^ 2 * (D z - D x) ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (hKnn z)
        _ = b ^ 2 * (K x z * (D z - D x) ^ 2) := by ring
  have hM3_abs : |M3| ≤ b * lv := by
    rw [hM3def, hlvdef, Finset.mul_sum]
    calc |∑ z, K x z * (D z - D x) ^ 3| ≤ ∑ z, |K x z * (D z - D x) ^ 3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, b * (K x z * (D z - D x) ^ 2) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hz : K x z = 0
          · rw [hz, zero_mul]; simp
          · have hb := hbinc z hz
            rw [abs_mul, abs_of_nonneg (hKnn z)]
            have hcube : |(D z - D x) ^ 3| ≤ b * (D z - D x) ^ 2 := by
              rw [show (D z - D x) ^ 3 = (D z - D x) * (D z - D x) ^ 2 by ring, abs_mul,
                abs_of_nonneg (sq_nonneg (D z - D x))]
              exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
            calc K x z * |(D z - D x) ^ 3| ≤ K x z * (b * (D z - D x) ^ 2) :=
                  mul_le_mul_of_nonneg_left hcube (hKnn z)
              _ = b * (K x z * (D z - D x) ^ 2) := by ring
  -- assemble
  rw [hexp]
  have hM3lo : -(b * lv) ≤ M3 := (abs_le.1 hM3_abs).1
  have hM3hi : M3 ≤ b * lv := (abs_le.1 hM3_abs).2
  -- 4 D x M3 ≤ 2 (D x)² b² + 2 b⁴ via |·| and AM-GM
  have hcross : 4 * (D x) * M3 ≤ 2 * (D x) ^ 2 * b ^ 2 + 2 * b ^ 4 := by
    have hbnd : (D x) * M3 ≤ |D x| * (b * lv) := by
      calc (D x) * M3 ≤ |(D x) * M3| := le_abs_self _
        _ = |D x| * |M3| := abs_mul _ _
        _ ≤ |D x| * (b * lv) := mul_le_mul_of_nonneg_left hM3_abs (abs_nonneg _)
    have hlb : |D x| * (b * lv) ≤ |D x| * b ^ 3 := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [hlv_le, hbnn, hlv_nn]
    nlinarith [hbnd, hlb, sq_nonneg (|D x| - b), sq_abs (D x), abs_nonneg (D x), hbnn,
      mul_nonneg (show (0:ℝ) ≤ 2 * b ^ 2 by positivity) (sq_nonneg (|D x| - b))]
  nlinarith [hlv_le, hlv_nn, hM4_le, sq_nonneg (D x), hbnn, hcross,
    mul_le_mul_of_nonneg_left hlv_le (show (0:ℝ) ≤ 6 * (D x) ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hlv_le (show (0:ℝ) ≤ b ^ 2 by positivity)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: telescoped second/fourth moment bounds

Telescoping the per-step bounds:
* upper quadratic variation `E[D_T²] ≤ E[D_0²] + b²·T`  (`sq_moment_le`, from `locVar ≤ b²`);
* fourth-moment growth `E[D_T⁴] − E[D_0⁴] ≤ ∑_{t<T} (8 b² E[D_t²] + 3 b⁴)`  (`fourth_moment_telescope_le`,
  from the per-step `fourth_drift_le`).

Together with the lower QV (`sq_moment_ge`) and Paley–Zygmund (`mean_sq_cubed_le`), these give
`E|D_T| ≥ c√T`, feeding the Tanaka occupation lower bound.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **Upper quadratic variation.** With `locVar ≤ b²`, `E[D_T²] ≤ E[D_0²] + b²·T`. -/
theorem sq_moment_le (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b2 : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hlv : ∀ x, locVar K D x ≤ b2) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 2) ≤ (∑ x, μ0 x * (D x) ^ 2) + b2 * T := by
  have htel := sq_moment_telescope K D μ0 hKsum hmart T
  have hle : ∀ t, (∑ x, distPow K μ0 t x * locVar K D x) ≤ b2 := by
    intro t
    calc ∑ x, distPow K μ0 t x * locVar K D x ≤ ∑ x, distPow K μ0 t x * b2 :=
          Finset.sum_le_sum (fun x _ =>
            mul_le_mul_of_nonneg_left (hlv x) (distPow_nonneg K μ0 hKnn hμ0nn t x))
      _ = b2 := by rw [← Finset.sum_mul, distPow_sum K μ0 hKsum hμ0sum t, one_mul]
  have hsum : (∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x) ≤ b2 * T := by
    calc (∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x)
        ≤ ∑ _t ∈ Finset.range T, b2 := Finset.sum_le_sum (fun t _ => hle t)
      _ = b2 * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  linarith [htel, hsum]

/-- **Fourth-moment telescoping.** -/
theorem fourth_moment_telescope_le (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4) - (∑ x, μ0 x * (D x) ^ 4)
      ≤ ∑ t ∈ Finset.range T, (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4) := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 4)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * (D z) ^ 4) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * (D z) ^ 4)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * (D z) ^ 4 from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 4)
        - (∑ x, distPow K μ0 T x * (D x) ^ 4)
        ≤ 8 * b ^ 2 * (∑ x, distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 := by
      rw [hswap, ← Finset.sum_sub_distrib]
      calc (∑ x, (distPow K μ0 T x * (∑ z, K x z * (D z) ^ 4) - distPow K μ0 T x * (D x) ^ 4))
          = ∑ x, distPow K μ0 T x * ((∑ z, K x z * (D z) ^ 4) - (D x) ^ 4) := by
            refine Finset.sum_congr rfl (fun x _ => by ring)
        _ ≤ ∑ x, distPow K μ0 T x * (8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4) :=
            Finset.sum_le_sum (fun x _ =>
              mul_le_mul_of_nonneg_left
                (fourth_drift_le K D b hbnn x (hKnn x) (hKsum x) (hmart x) (hbinc x))
                (distPow_nonneg K μ0 hKnn hμ0nn T x))
        _ = 8 * b ^ 2 * (∑ x, distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 := by
            rw [Finset.sum_congr rfl (fun x _ =>
              show distPow K μ0 T x * (8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4)
                = 8 * b ^ 2 * (distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 * distPow K μ0 T x from by
                ring)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              distPow_sum K μ0 hKsum hμ0sum T, mul_one]
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: assembling the occupation lower bound

Closed-form fourth-moment bound `E[D_T⁴] ≤ E[D_0⁴] + 8b²E[D_0²]·T + 8b⁴·T² + 3b⁴·T` (substituting the
upper QV into the fourth-moment telescoping), plus the reusable local-variance bound `locVar ≤ b²`.
These feed the Paley–Zygmund anti-concentration to give `E|D_T| → ∞`, hence (via Tanaka) the window
occupation `→ ∞`.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Local variance is bounded by the squared increment bound. -/
lemma locVar_le (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (x : ι) (hKnn : ∀ z, 0 ≤ K x z)
    (hKsum : ∑ z, K x z = 1) (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    locVar K D x ≤ b ^ 2 := by
  unfold locVar
  calc ∑ z, K x z * (D z - D x) ^ 2 ≤ ∑ z, K x z * b ^ 2 := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
          have := hbinc z hz
          nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), this]
    _ = b ^ 2 := by rw [← Finset.sum_mul, hKsum, one_mul]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {ι : Type*} [Fintype ι]
theorem solution (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4)
      ≤ (∑ x, μ0 x * (D x) ^ 4) + 8 * b ^ 2 * (∑ x, μ0 x * (D x) ^ 2) * T
        + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by
  have htel := fourth_moment_telescope_le K D μ0 b hbnn hKnn hKsum hmart hbinc hμ0nn hμ0sum T
  have hlv : ∀ x, locVar K D x ≤ b ^ 2 := fun x => locVar_le K D b x (hKnn x) (hKsum x) (hbinc x)
  set E0 := ∑ x, μ0 x * (D x) ^ 2 with hE0
  have hbound : (∑ t ∈ Finset.range T,
        (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4))
      ≤ 8 * b ^ 2 * E0 * T + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by
    calc (∑ t ∈ Finset.range T,
            (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4))
        ≤ ∑ _t ∈ Finset.range T, (8 * b ^ 2 * E0 + 8 * b ^ 4 * (T : ℝ) + 3 * b ^ 4) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          have hsq := sq_moment_le K D μ0 (b ^ 2) hKnn hKsum hmart hμ0nn hμ0sum hlv t
          have htle : (t : ℝ) ≤ T := by exact_mod_cast le_of_lt (Finset.mem_range.1 ht)
          have hb2 : (0 : ℝ) ≤ 8 * b ^ 2 := by positivity
          have hb4 : (0 : ℝ) ≤ 8 * b ^ 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hsq hb2, mul_le_mul_of_nonneg_left htle hb4]
      _ = (8 * b ^ 2 * E0 + 8 * b ^ 4 * (T : ℝ) + 3 * b ^ 4) * T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ = 8 * b ^ 2 * E0 * T + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by ring
  linarith [htel, hbound]
