-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka_loc
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:28:09.00774+00:00
-- url     : https://prove2.me/submissions/aec253d0-f931-4b5a-b950-8bd87b546b85

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: single-step Tanaka drift of `|D|` (deterministic substrate)

For the rank-difference walk `D` under a stochastic kernel `K` that is *mean-preserving* (a martingale,
`∑_z K x z · D z = D x`) with *bounded increments* (`K x z ≠ 0 → |D z − D x| ≤ b`), the absolute value
`|D|` is a submartingale whose one-step drift is supported on the window `{|D| ≤ b}`:

  `0 ≤ ∑_z K x z |D z| − |D x| ≤ b`,  and `= 0` when `|D x| > b`.

This is the per-step heart of the Tanaka decomposition `E|D_T| = E|D_0| + (compensator)`, where the
compensator equals the window local time.  Telescoped, it gives `window-occupation ≥ (E|D_T| − E|D_0|)/b`,
which with the Paley–Zygmund bound `E|D_T| ≥ c√T` (brick 84) yields the occupation lower bound.  All in
the deterministic finite-sum substrate — no measure theory.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)

/-- **Bounded drift:** the step increases `|D|` by at most the increment bound `hb`. -/
theorem abs_drift_le (hb : ℝ) (x : ι) (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ hb) :
    (∑ z, K x z * |D z|) ≤ |D x| + hb := by
  have hstep : ∑ z, K x z * |D z| ≤ ∑ z, K x z * (|D x| + hb) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz : K x z = 0
    · rw [hz]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
      calc |D z| = |D x + (D z - D x)| := by congr 1; ring
        _ ≤ |D x| + |D z - D x| := abs_add_le _ _
        _ ≤ |D x| + hb := by linarith [hbinc z hz]
  calc ∑ z, K x z * |D z| ≤ ∑ z, K x z * (|D x| + hb) := hstep
    _ = (∑ z, K x z) * (|D x| + hb) := by rw [Finset.sum_mul]
    _ = |D x| + hb := by rw [hKsum]; ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: localized (off-window) Tanaka occupation bound

The conditioned residual walk has a bounded REPELLING drift on the window, but is the product walk
(approximate martingale) OFF the window.  The Tanaka `|D|`-drift bound needs the drift `≤ η` only OFF the
window (`b < |D x|`); on-window the per-step `|D|`-drift is `≤ b` regardless of the drift (triangle
inequality).  So the occupation bound `E|D_T| − E|D_0| ≤ b·(window occupation) + η·T` holds with only the
off-window drift hypothesis.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Localized per-step `|D|`-drift: bounded by `b` on `{|D| ≤ b}` and by `η` off it (off-window drift
hypothesis only). -/
lemma abs_drift_le_indic_off (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (x : α) (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hdrift_off : b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * |D z|) - |D x| ≤ b * (if |D x| ≤ b then (1 : ℝ) else 0) + η := by
  by_cases hle : |D x| ≤ b
  · rw [if_pos hle, mul_one]
    linarith [abs_drift_le K D b x hKnn hKsum hbinc, hηnn]
  · rw [if_neg hle, mul_zero, zero_add]
    push_neg at hle
    rcases abs_le.1 (hdrift_off hle) with ⟨hlo, hhi⟩
    rcases lt_trichotomy (D x) 0 with hneg | hzero | hpos
    · have habs : |D x| = -D x := abs_of_neg hneg
      have hsum : (∑ z, K x z * |D z|) = -(∑ z, K x z * D z) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul, neg_zero]
        · have hbz := abs_le.1 (hbinc z hz)
          have hdz : D z < 0 := by rw [habs] at hle; linarith [hbz.2]
          rw [abs_of_neg hdz]; ring
      rw [hsum, habs]; linarith [hlo]
    · exfalso; rw [hzero] at hle; simp at hle; linarith [hbnn]
    · have habs : |D x| = D x := abs_of_pos hpos
      have hsum : (∑ z, K x z * |D z|) = ∑ z, K x z * D z := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul]
        · have hbz := abs_le.1 (hbinc z hz)
          have hdz : 0 < D z := by rw [habs] at hle; linarith [hbz.1]
          rw [abs_of_pos hdz]
      rw [hsum, habs]; linarith [hhi]

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass in
theorem solution (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (μ0 : α → ℝ) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0sum : ∑ x, μ0 x = 1)
    (hdrift_off : ∀ x, b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (T : ℕ) :
    (∑ x, distPow K μ0 T x * |D x|) - (∑ x, μ0 x * |D x|)
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η * T := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * |D x|)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * |D z|) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * |D z|)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * |D z| from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (∑ x, distPow K μ0 (T + 1) x * |D x|) - (∑ x, distPow K μ0 T x * |D x|)
        ≤ b * (∑ x, distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η := by
      rw [hswap, ← Finset.sum_sub_distrib]
      calc (∑ x, (distPow K μ0 T x * (∑ z, K x z * |D z|) - distPow K μ0 T x * |D x|))
          ≤ ∑ x, distPow K μ0 T x * (b * (if |D x| ≤ b then (1 : ℝ) else 0) + η) := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left
              (abs_drift_le_indic_off K D b η hbnn hηnn x (hKnn x) (hKsum x) (hdrift_off x) (hbinc x))
              (distPow_nonneg K μ0 hKnn hμ0nn T x)
        _ = b * (∑ x, distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η := by
            rw [Finset.sum_congr rfl (fun x _ =>
              show distPow K μ0 T x * (b * (if |D x| ≤ b then (1:ℝ) else 0) + η)
                = b * (distPow K μ0 T x * (if |D x| ≤ b then (1:ℝ) else 0)) + η * distPow K μ0 T x from by
                ring)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              distPow_sum K μ0 hKsum hμ0sum T, mul_one]
    rw [Finset.sum_range_succ, mul_add]
    push_cast
    nlinarith [ih, hstep]
