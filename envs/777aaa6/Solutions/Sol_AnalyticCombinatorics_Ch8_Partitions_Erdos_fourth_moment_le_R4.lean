-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_R4
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:28:18.087794+00:00
-- url     : https://prove2.me/submissions/eccbd689-b1e3-446f-935a-ee0e93362240

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
# R7 Fact B via Doeblin: η-robust occupation capstone

For the η-approximate-martingale Erdős rank-difference walk, the window occupation is still unbounded.
The fourth moment is bounded *trivially* by `R⁴` (since `|D| ≤ R`), so Paley–Zygmund with the linear
lower QV `E[D_T²] ≥ (v₀−2Rη)·T` gives `(E|D_T|)² ≥ ((v₀−2Rη)T)³/R⁴ → ∞` (cubic) — no re-derived
fourth-moment bound needed.  Combined with the η-robust Tanaka bound `occ ≥ (E|D_T| − E|D_0| − ηT)/b`,
and since `E|D_T| ~ T^{3/2} ≫ ηT`, the occupation exceeds any target.  Deterministic finite-sum.
Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Finset
variable {ι : Type*} [Fintype ι]
theorem solution (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (R : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hμ0nn : ∀ x, 0 ≤ μ0 x)
    (hμ0sum : ∑ x, μ0 x = 1) (hR : ∀ x, |D x| ≤ R) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ R ^ 4 := by
  calc (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ ∑ x, distPow K μ0 T x * R ^ 4 := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (distPow_nonneg K μ0 hKnn hμ0nn T x)
        have hd4 : (D x) ^ 4 = |D x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [hd4]; exact pow_le_pow_left₀ (abs_nonneg _) (hR x) 4
    _ = R ^ 4 := by rw [← Finset.sum_mul, distPow_sum K μ0 hKsum hμ0sum T, one_mul]
