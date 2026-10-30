-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.truncated_block_heat_transfer
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:19:23.50084+00:00
-- url     : https://prove2.me/submissions/463f0737-5f7e-4dfe-89c6-0dc1b0b5a574

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

section
/-!
# L¹ stability of Markov evolution (occupation transfer)

If two stochastic kernels `K`, `K'` are within per-step `L¹` distance `ε` (i.e.
`∀ x, ∑_z |K x z − K' x z| ≤ ε`), then their `t`-step laws from a common start are within `t·ε`:

  `∑_z |distPow K μ₀ t z − distPow K' μ₀ t z| ≤ t·ε`.

This is the route-independent transfer primitive: it lets occupation lower bounds proved for a
truncated kernel `K'` be transported to the original soft-tailed kernel `K`, the discrepancy over a
horizon `M` being `≤ ε·∑_{t<M} t`.  Deterministic finite-sum.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **L¹ stability:** the `t`-step laws of two stochastic kernels within per-step `L¹` distance `ε`
differ by at most `t·ε` in `L¹`. -/
lemma distPow_L1_le (K K' : ι → ι → ℝ) (μ0 : ι → ℝ) (ε : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hK'nn : ∀ x z, 0 ≤ K' x z) (hK'sum : ∀ x, ∑ z, K' x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - K' x z|) ≤ ε) :
    ∀ t, (∑ z, |distPow K μ0 t z - distPow K' μ0 t z|) ≤ t * ε := by
  intro t
  induction t with
  | zero => simp [distPow]
  | succ t ih =>
    -- per-coordinate split
    have hz : ∀ z, |distPow K μ0 (t + 1) z - distPow K' μ0 (t + 1) z|
        ≤ (∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * K x z)
          + ∑ x, distPow K' μ0 t x * |K x z - K' x z| := by
      intro z
      simp only [distPow]
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun x _ => ?_)
      have hsplit : distPow K μ0 t x * K x z - distPow K' μ0 t x * K' x z
          = (distPow K μ0 t x - distPow K' μ0 t x) * K x z
            + distPow K' μ0 t x * (K x z - K' x z) := by ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hKnn x z),
        abs_of_nonneg (distPow_nonneg K' μ0 hK'nn hμ0nn t x)]
    -- sum over z and use sum_comm
    calc (∑ z, |distPow K μ0 (t + 1) z - distPow K' μ0 (t + 1) z|)
        ≤ ∑ z, ((∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * K x z)
            + ∑ x, distPow K' μ0 t x * |K x z - K' x z|) := Finset.sum_le_sum (fun z _ => hz z)
      _ = (∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * (∑ z, K x z))
            + ∑ x, distPow K' μ0 t x * (∑ z, |K x z - K' x z|) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          · exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
      _ ≤ (∑ x, |distPow K μ0 t x - distPow K' μ0 t x|) + ε := by
          refine add_le_add (le_of_eq ?_) ?_
          · exact Finset.sum_congr rfl (fun x _ => by rw [hKsum x, mul_one])
          · calc (∑ x, distPow K' μ0 t x * (∑ z, |K x z - K' x z|))
                ≤ ∑ x, distPow K' μ0 t x * ε :=
                  Finset.sum_le_sum (fun x _ =>
                    mul_le_mul_of_nonneg_left (hclose x) (distPow_nonneg K' μ0 hK'nn hμ0nn t x))
              _ = ε := by rw [← Finset.sum_mul, distPow_sum K' μ0 hK'sum hμ0sum t, one_mul]
      _ ≤ t * ε + ε := by linarith [ih]
      _ = (↑(t + 1)) * ε := by push_cast; ring

/-- **Occupation transfer:** a window-occupation lower bound for `K'` transfers to `K`, up to the
discrepancy `(∑_{t<M} t)·ε`.  (So `occ_K ≥ occ_{K'} − (∑t)·ε`.) -/
lemma occupation_transfer (K K' : ι → ι → ℝ) (μ0 : ι → ℝ) (D : ι → ℝ) (b ε : ℝ) (M : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hK'nn : ∀ x z, 0 ≤ K' x z) (hK'sum : ∀ x, ∑ z, K' x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - K' x z|) ≤ ε) :
    (∑ t ∈ Finset.range M, ∑ x, distPow K' μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
      - (∑ t ∈ Finset.range M, ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
      ≤ (∑ t ∈ Finset.range M, (t : ℝ)) * ε := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hL1 : (∑ z, |distPow K' μ0 t z - distPow K μ0 t z|) ≤ t * ε :=
    distPow_L1_le K' K μ0 ε hK'nn hK'sum hKnn hKsum hμ0nn hμ0sum
      (fun x => by simpa [abs_sub_comm] using hclose x) t
  calc (∑ x, distPow K' μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
        - ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)
      = ∑ x, (distPow K' μ0 t x - distPow K μ0 t x) * (if |D x| ≤ b then (1 : ℝ) else 0) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)
    _ ≤ ∑ x, |distPow K' μ0 t x - distPow K μ0 t x| := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        by_cases h : |D x| ≤ b
        · rw [if_pos h, mul_one]; exact le_abs_self _
        · rw [if_neg h, mul_zero]; exact abs_nonneg _
    _ ≤ t * ε := hL1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Truncation transfer (renewal route B, Layer-2 steps A & C)

The Erdős rank-difference kernel is soft/nonlocal, but its rank-drop tail is *exponential*
(`RankDropKer.Pker_rankDrop_tail_majorant`, `γ = C/60`).  The Layer-2 block-heat lower bound is
therefore proved for a *truncated* kernel (jumps capped at `L_m ≍ log m`, mass renormalized) and
transferred back to the real kernel via the banked `OccupationTransfer.occupation_transfer`
(`L¹`-distance `t·ε` over a horizon).  This file banks the two kernel-agnostic, finite-sum bridges:

* `normalize_truncate_L1_eq_two_tail` — the per-row `L¹` distance between a probability row and its
  normalized truncation `P' = P·1_Good/q` is exactly `2·τ`, where `τ` is the truncated tail mass.
* `truncated_block_heat_transfer` — a truncated block-heat lower bound `c0/√(M+1)` transfers to the
  real kernel as `c0/(2√(M+1))`, provided the cumulative `L¹` error `(∑_{t<M} t)·ε ≤ c0/(2√(M+1))`.

(Route + constants from ChatGPT ac2 R9, verified against the repo's `occupation_transfer` /
`Pker_rankDrop_tail_majorant`.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem solution
    (K Ktr : α → α → ℝ) (μ0 : α → ℝ) (D : α → ℝ)
    (W c0 ε : ℝ) (M : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hKtrnn : ∀ x z, 0 ≤ Ktr x z) (hKtrsum : ∀ x, ∑ z, Ktr x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - Ktr x z|) ≤ ε)
    (htrunc :
      c0 / Real.sqrt ((M : ℝ) + 1)
        ≤ ∑ t ∈ Finset.range M,
            ∑ x, distPow Ktr μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0))
    (herr :
      (∑ t ∈ Finset.range M, (t : ℝ)) * ε
        ≤ c0 / (2 * Real.sqrt ((M : ℝ) + 1))) :
    c0 / (2 * Real.sqrt ((M : ℝ) + 1))
      ≤ ∑ t ∈ Finset.range M,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0) := by
  have htrans :=
    occupation_transfer K Ktr μ0 D W ε M
      hKnn hKsum hKtrnn hKtrsum hμ0nn hμ0sum hclose
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hrel : 2 * (c0 / (2 * Real.sqrt ((M : ℝ) + 1))) = c0 / Real.sqrt ((M : ℝ) + 1) := by
    field_simp
  linarith [htrunc, herr, htrans, hrel]
