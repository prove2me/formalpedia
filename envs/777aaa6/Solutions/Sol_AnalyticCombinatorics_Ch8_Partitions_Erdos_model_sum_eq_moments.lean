-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_eq_moments
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:26.670522+00:00
-- url     : https://prove2.me/submissions/28fd7713-5af3-4a18-8e7e-993431649b1b

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

lemma sigmaR_le_square {n : ℕ} (hn : 1 ≤ n) :
    Sigma.sigmaR n ≤ (n : ℝ) ^ 2 := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  have hcard_nat : n.divisors.card ≤ n := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by
        simp
  have hsum_le :
      (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
  calc
    (∑ d ∈ n.divisors, (d : ℝ))
        ≤ ∑ _d ∈ n.divisors, (n : ℝ) := hsum_le
    _ = (n.divisors.card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (n : ℝ) ^ 2 := by
          have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_nat
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          nlinarith

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Mass-rate campaign: the Lambert identity for `M₀` (R8 §2.1)

`M₀(t) = Σ_m σ(m)e^{−tm} = Σ_k boseKernel(tk)` — via Mathlib's
`tsum_prod_pow_eq_tsum_sigma` (divisors-antidiagonal Lambert machinery from the
Eisenstein q-expansion development) at `k = 1`, `r = e^{−t}`, with the
geometric-derivative inner sum `Σ'_{c:ℕ+} c·y^c = y/(1−y)²`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology ArithmeticFunction.sigma

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `σR` agrees with the arithmetic-function `σ 1` (cast). -/
lemma sigmaR_eq_sigma_one (m : ℕ) : Sigma.sigmaR m = ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) := rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the `M₁` Lambert identity by termwise differentiation

`M₁(t) = Σ_k k·boseKernel2(tk)`, `boseKernel2(z) = e^{−z}(1+e^{−z})/(1−e^{−z})³ = Σ_d d²e^{−dz}`
— obtained by differentiating both sides of the banked `M₀` Lambert identity termwise on
`Ioi (t/2)` via `hasDerivAt_tsum_of_isPreconnected`, then `HasDerivAt.unique`.
Replaces the retired antidiagonal draft.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Summability of `m^j·σ(m)·r^m` for `‖r‖ < 1`. -/
lemma summable_pow_sigma_geometric (j : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m) := by
  have hr' : ‖|r|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_abs]
    rwa [Real.norm_eq_abs] at hr
  have hbig := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (j + 2) hr'
  refine Summable.of_nonneg_of_le
    (f := fun m : ℕ => ((m : ℝ)) ^ (j + 2) * |r| ^ m) (fun m => ?_) (fun m => ?_) hbig
  · have := sigmaR_nonneg m
    positivity
  ·
    by_cases hm : m = 0
    · subst hm
      have hσ0 : Sigma.sigmaR 0 = 0 := by
        rw [sigmaR_eq_sigma_one]
        simp
      simp only [hσ0, Nat.cast_zero, mul_zero, zero_mul]
      positivity
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hσ : Sigma.sigmaR m ≤ (m : ℝ) ^ 2 := sigmaR_le_square hm1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have habs : (0 : ℝ) ≤ |r| ^ m := by positivity
      calc (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m
          ≤ (m : ℝ) ^ j * (m : ℝ) ^ 2 * |r| ^ m := by
            apply mul_le_mul_of_nonneg_right _ habs
            exact mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = (m : ℝ) ^ (j + 2) * |r| ^ m := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-- `modelSummand·rhoDropModel = σ·e^{−tm}·(c₁·m + c₂·m² + c₃·m³ + c₄·m⁴)` with
  `c₁ = 3/(2·n·√n)`, `c₂ = 15/(8·n²·√n)`, `c₃ = 3/(8·n²·(√n)³) − 3·C/(16·n³)`,
  `c₄ = −3·C/(64·n⁴)`. -/
lemma modelSummand_mul_rhoDropModel_expand {n m : ℕ} (hm : m ≠ 0) :
    modelSummand n m * rhoDropModel n m
    = Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))
    * ( (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * (m:ℝ)
      + ((15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (m:ℝ) ^ 2)
      + (((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3))
         - 3 * C / (16 * (n:ℝ) ^ 3)) * (m:ℝ) ^ 3)
      + ((-3 * C / (64 * (n:ℝ) ^ 4)) * (m:ℝ) ^ 4)) := by
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  have hs2 : s ^ 2 = (n : ℝ) := by
    rw [hs]
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  rw [modelSummand, rhoDropModel, if_neg hm]
  rw [← hs, ← hs2]
  ring

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

private lemma sigmaR_zero_mu : Sigma.sigmaR 0 = 0 := by
  simp [Sigma.sigmaR]

/-- Summability of the divisor-weighted Lambert summand. -/
private lemma summable_sigma_exp_mu (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else
        (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h
    simp [sigmaR_zero_mu]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000
open Filter Finset
open scoped Topology BigOperators
theorem solution (n : ℕ) (hn1 : 1 ≤ n) :
    (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
    = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
    + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
    + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
       - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
    + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set t : ℝ := massLam / Real.sqrt (n:ℝ) with htdef
  let f : ℕ → ℕ → ℝ := fun k m =>
    if m = 0 then (0:ℝ) else
      (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))
  have hsum (k : ℕ) : Summable (f k) := by
    dsimp [f]
    exact summable_sigma_exp_mu k ht0
  let c1 : ℝ := 3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))
  let c2 : ℝ := 15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))
  let c3 : ℝ := 3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3) - 3 * C / (16 * (n:ℝ) ^ 3)
  let c4 : ℝ := -3 * C / (64 * (n:ℝ) ^ 4)
  have hf1 : Summable (fun m : ℕ => c1 * f 1 m) := (hsum 1).mul_left c1
  have hf2 : Summable (fun m : ℕ => c2 * f 2 m) := (hsum 2).mul_left c2
  have hf3 : Summable (fun m : ℕ => c3 * f 3 m) := (hsum 3).mul_left c3
  have hf4 : Summable (fun m : ℕ => c4 * f 4 m) := (hsum 4).mul_left c4
  have hf1eq : (∑' m : ℕ, c1 * f 1 m) = c1 * sigmaMoment 1 t := by
    rw [sigmaMoment, ← tsum_mul_left]
  have hf2eq : (∑' m : ℕ, c2 * f 2 m) = c2 * sigmaMoment 2 t := by
    rw [sigmaMoment, ← tsum_mul_left]
  have hf3eq : (∑' m : ℕ, c3 * f 3 m) = c3 * sigmaMoment 3 t := by
    rw [sigmaMoment, ← tsum_mul_left]
  have hf4eq : (∑' m : ℕ, c4 * f 4 m) = c4 * sigmaMoment 4 t := by
    rw [sigmaMoment, ← tsum_mul_left]
  calc
    (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
        = (∑' m : ℕ, (c1 * f 1 m + c2 * f 2 m + (c3 * f 3 m + c4 * f 4 m))) := by
          apply tsum_congr
          intro m
          by_cases hm : m = 0
          · simp [hm, f]
          · rw [if_neg hm, modelSummand_mul_rhoDropModel_expand hm]
            simp [f, c1, c2, c3, c4, htdef, hm]
            ring
    _ = (∑' m : ℕ, c1 * f 1 m) + (∑' m : ℕ, c2 * f 2 m)
        + (∑' m : ℕ, c3 * f 3 m) + (∑' m : ℕ, c4 * f 4 m) := by
          rw [← hf1.tsum_add hf2]
          rw [← (hf1.add hf2).tsum_add hf3]
          rw [← ((hf1.add hf2).add hf3).tsum_add hf4]
          apply tsum_congr
          intro m
          ring
    _ = c1 * sigmaMoment 1 t + c2 * sigmaMoment 2 t
        + (c3 * sigmaMoment 3 t + c4 * sigmaMoment 4 t) := by
          rw [hf1eq, hf2eq, hf3eq, hf4eq]
          ring
    _ = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
      + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
      + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
         - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
      + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))) := by
          simp [c1, c2, c3, c4, htdef]
