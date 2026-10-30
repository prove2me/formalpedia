-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.model_rhoDropModel_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:22.314261+00:00
-- url     : https://prove2.me/submissions/9c80807b-b415-4775-874c-dfc2563939de

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_assembly_abs_add_three_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_le_power_sharp
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

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

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

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

section
/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- Exp beats poly with a sixth-root exponent: `(n:ℝ)^d · exp(−a·n^{1/6}) ≤ 1/n` eventually. The
analytic engine for both the far-`erdosWeight` tail and the `modelSummand` tail (cutoff `⌊n^{2/3}⌋`,
`t·⌊n^{2/3}⌋ ≍ n^{1/6}`). -/
lemma poly_mul_exp_neg_sixthRoot_le_inv (a : ℝ) (ha : 0 < a) (d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 / (n:ℝ) := by
  have htend : Filter.Tendsto
      (fun n : ℕ => (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto
        (fun x : ℝ => x ^ ((6 * (d + 1) : ℕ) : ℝ) * Real.exp (-a * x))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
    have hroot : Filter.Tendsto (fun n : ℕ => (n:ℝ) ^ (1/6 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine (hreal.comp hroot).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hpow : ((n:ℝ) ^ (1/6 : ℝ)) ^ ((6 * (d + 1) : ℕ) : ℝ) = (n:ℝ) ^ (d + 1) := by
      rw [← Real.rpow_mul hn0,
        show (1/6 : ℝ) * ((6 * (d + 1) : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    simp only [Function.comp]
    rw [hpow]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 :=
    htend.eventually_le_const (by norm_num)
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnpos]
  have hrw : (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) * (n:ℝ)
      = (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) := by ring
  rw [hrw]; exact hn1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

private lemma assembly_abs_add_four_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := assembly_abs_add_three_le a b c
  nlinarith

private lemma assembly_summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0 : ℝ) else
        (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h
    simp [Sigma.sigmaR]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]

/-- The model Lambert tail after the cutoff `M`. -/
private def assemblyGTail (n M k m : ℕ) : ℝ :=
  if m ≤ M then (0 : ℝ)
  else if m = 0 then (0 : ℝ)
  else (m : ℝ) ^ k * Sigma.sigmaR m *
    Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))

private lemma assemblyGTail_nonneg (n M k m : ℕ) :
    0 ≤ assemblyGTail n M k m := by
  rw [assemblyGTail]
  split
  · rfl
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le

private lemma assembly_summable_gTail (n M k : ℕ)
    {t : ℝ} (ht : massLam / Real.sqrt (n : ℝ) = t) (htp : 0 < t) :
    Summable (fun m => assemblyGTail n M k m) := by
  refine Summable.of_nonneg_of_le (assemblyGTail_nonneg n M k) (fun m => ?_)
    (assembly_summable_sigma_exp k htp)
  rw [assemblyGTail, ← ht]
  split
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  · exact le_rfl

private lemma assemblyGTail_eq_bare (n M k : ℕ) :
    (∑' m : ℕ, assemblyGTail n M k m)
      = ∑' m : ℕ, (if m ≤ M then (0 : ℝ)
          else (m : ℝ) ^ k * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
  apply tsum_congr
  intro m
  rw [assemblyGTail]
  rcases le_or_gt m M with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]

/-- Geometric extraction for the divisor-weighted Lambert tail. -/
private lemma assembly_sigma_geom_tail_le (k : ℕ) {t : ℝ} (ht : 0 < t) (M : ℕ) :
    (∑' m : ℕ, (if m ≤ M then (0 : ℝ)
        else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))))
      ≤ Real.exp (-(t / 2) * (M : ℝ)) * sigmaMoment k (t / 2) := by
  have ht2 : 0 < t / 2 := by linarith
  have hg0 := assembly_summable_sigma_exp k ht
  have hg2 := assembly_summable_sigma_exp k ht2
  set f : ℕ → ℝ := fun m => if m ≤ M then (0 : ℝ)
      else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)) with hfdef
  set g : ℕ → ℝ := fun m => Real.exp (-(t / 2) * (M : ℝ)) *
      (if m = 0 then (0 : ℝ) else
        (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) with hgdef
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m
    rw [hfdef]
    dsimp only
    split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  have hfle0 : ∀ m, f m ≤ (if m = 0 then (0 : ℝ)
      else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
    intro m
    rw [hfdef]
    dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
  have hfsumm : Summable f := Summable.of_nonneg_of_le hfnn hfle0 hg0
  have hgsumm : Summable g := hg2.mul_left _
  have hbound : ∀ m, f m ≤ g m := by
    intro m
    rw [hfdef, hgdef]
    dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      apply mul_nonneg (Real.exp_pos _).le
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
      have hexp : Real.exp (-t * (m : ℝ))
          ≤ Real.exp (-(t / 2) * (M : ℝ)) * Real.exp (-(t / 2) * (m : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.le
        nlinarith [hmM, ht]
      calc
        (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
            ≤ (m : ℝ) ^ k * Sigma.sigmaR m *
                (Real.exp (-(t / 2) * (M : ℝ)) * Real.exp (-(t / 2) * (m : ℝ))) :=
              mul_le_mul_of_nonneg_left hexp
                (mul_nonneg (by positivity) (sigmaR_nonneg m))
        _ = Real.exp (-(t / 2) * (M : ℝ)) *
              ((m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) := by ring
  calc
    (∑' m, f m) ≤ ∑' m : ℕ, g m := Summable.tsum_le_tsum hbound hfsumm hgsumm
    _ = Real.exp (-(t / 2) * (M : ℝ)) *
          ∑' m : ℕ, (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) := by
        rw [hg2.tsum_mul_left (Real.exp (-(t / 2) * (M : ℝ)))]
    _ = Real.exp (-(t / 2) * (M : ℝ)) * sigmaMoment k (t / 2) := by
        rw [sigmaMoment]

private lemma model_product_abs_le (n m : ℕ) :
    |modelSummand n m * rhoDropModel n m|
      ≤ (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 1 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 2 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 3 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    simp [modelSummand]
  · rw [modelSummand_mul_rhoDropModel_expand hm]
    set base : ℝ := Sigma.sigmaR m *
      Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)) with hbase
    have hbase_nonneg : 0 ≤ base := by
      rw [hbase]
      exact mul_nonneg (sigmaR_nonneg m) (Real.exp_pos _).le
    set a1 : ℝ := (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ) with ha1
    set a2 : ℝ := (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2 with ha2
    set a3 : ℝ := (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)) * (m : ℝ) ^ 3 with ha3
    set b3 : ℝ := (3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3 with hb3
    set a4 : ℝ := (3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4 with ha4
    have ha1nn : 0 ≤ a1 := by rw [ha1]; positivity
    have ha2nn : 0 ≤ a2 := by rw [ha2]; positivity
    have ha3nn : 0 ≤ a3 := by rw [ha3]; positivity
    have hb3nn : 0 ≤ b3 := by rw [hb3]; have := C_pos; positivity
    have ha4nn : 0 ≤ a4 := by rw [ha4]; have := C_pos; positivity
    have hpoly :
        |a1 + a2 + (a3 - b3) + (-a4)| ≤ a1 + a2 + (a3 + b3) + a4 := by
      calc
        |a1 + a2 + (a3 - b3) + (-a4)|
            ≤ |a1| + |a2| + |a3 - b3| + |-a4| :=
              assembly_abs_add_four_le a1 a2 (a3 - b3) (-a4)
        _ ≤ a1 + a2 + (a3 + b3) + a4 := by
          have hsub : |a3 - b3| ≤ a3 + b3 := by
            rw [abs_le]
            constructor <;> nlinarith
          rw [abs_of_nonneg ha1nn, abs_of_nonneg ha2nn, abs_neg, abs_of_nonneg ha4nn]
          linarith
    have hrewrite :
        ( (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ)
          + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2
          + ((3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
              - 3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3)
          + ((-3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4))
        = a1 + a2 + (a3 - b3) + (-a4) := by
      rw [ha1, ha2, ha3, hb3, ha4]
      ring
    calc
      |base *
          ( (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ)
            + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2
            + ((3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
                - 3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3)
            + ((-3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4))|
          = base *
              |a1 + a2 + (a3 - b3) + (-a4)| := by
            rw [hrewrite, abs_mul, abs_of_nonneg hbase_nonneg]
      _ ≤ base * (a1 + a2 + (a3 + b3) + a4) :=
            mul_le_mul_of_nonneg_left hpoly hbase_nonneg
      _ =
        (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          ((m : ℝ) ^ 1 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          ((m : ℝ) ^ 2 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          ((m : ℝ) ^ 3 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          ((m : ℝ) ^ 4 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
            rw [hbase, ha1, ha2, ha3, hb3, ha4]
            ring
      _ =
        (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 1 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 2 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 3 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
            rw [if_neg hm, if_neg hm, if_neg hm, if_neg hm]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
set_option maxHeartbeats 8000000 in
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑' m : ℕ,
        if m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ then (0 : ℝ)
        else |modelSummand n m * rhoDropModel n m|)
      ≤ K / (n : ℝ) := by
  obtain ⟨K1, hK1nn, hK1⟩ := sigmaMoment_le_power_sharp 1
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  have hlam0 : 0 < massLam := massLam_pos
  have hCpos : 0 < C := C_pos
  set B : ℝ :=
    12 * K1 / massLam ^ 3
      + 30 * K2 / massLam ^ 4
      + (12 + 6 * C) * K3 / massLam ^ 5
      + 3 * C * K4 / massLam ^ 6 with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    positivity
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sixthRoot_le_inv (massLam / 4) (by positivity) 0,
    Filter.eventually_ge_atTop (max 8 ⌈massLam ^ 2⌉₊)] with n hpoly hnge
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hnge
  have hnlamc : ⌈massLam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hnge
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hnge1
  have htp : 0 < massLam / Real.sqrt (n : ℝ) := div_pos hlam0 hs0
  have hlamle : massLam ≤ Real.sqrt (n : ℝ) := by
    calc
      massLam = Real.sqrt (massLam ^ 2) := (Real.sqrt_sq hlam0.le).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by
        have : (⌈massLam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlamc
        linarith [Nat.le_ceil (massLam ^ 2)])
  have ht2pos : 0 < massLam / Real.sqrt (n : ℝ) / 2 := by positivity
  have ht2le1 : massLam / Real.sqrt (n : ℝ) / 2 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]
    nlinarith [hlamle, hs1, hlam0]
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hsummgT : ∀ k, Summable (fun m => assemblyGTail n M k m) :=
    fun k => assembly_summable_gTail n M k rfl htp
  let c1 : ℝ := 3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))
  let c2 : ℝ := 15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))
  let c3 : ℝ := 3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
    + 3 * C / (16 * (n : ℝ) ^ 3)
  let c4 : ℝ := 3 * C / (64 * (n : ℝ) ^ 4)
  have hpt : ∀ m,
      (if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
          + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m := by
    intro m
    by_cases hmM : m ≤ M
    · simp [hmM, assemblyGTail, c1, c2, c3, c4]
    · rw [if_neg hmM, assemblyGTail, assemblyGTail, assemblyGTail, assemblyGTail,
        if_neg hmM, if_neg hmM, if_neg hmM, if_neg hmM]
      simpa [c1, c2, c3, c4] using model_product_abs_le n m
  have hdomsumm : Summable (fun m => c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
      + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m) := by
    refine ((((hsummgT 1).mul_left c1).add ((hsummgT 2).mul_left c2)).add
      ((hsummgT 3).mul_left c3)).add ((hsummgT 4).mul_left c4) |>.congr ?_
    intro m
    ring
  have htailsumm : Summable (fun m : ℕ =>
      if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|) :=
    Summable.of_nonneg_of_le (fun m => by split <;> positivity) hpt hdomsumm
  have hsplit :
      (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := by
    calc
      (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
          ≤ ∑' m : ℕ, (c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
              + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m) :=
            Summable.tsum_le_tsum hpt htailsumm hdomsumm
      _ = c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := by
            let f1 : ℕ → ℝ := fun m => c1 * assemblyGTail n M 1 m
            let f2 : ℕ → ℝ := fun m => c2 * assemblyGTail n M 2 m
            let f3 : ℕ → ℝ := fun m => c3 * assemblyGTail n M 3 m
            let f4 : ℕ → ℝ := fun m => c4 * assemblyGTail n M 4 m
            have hf1 : Summable f1 := (hsummgT 1).mul_left c1
            have hf2 : Summable f2 := (hsummgT 2).mul_left c2
            have hf3 : Summable f3 := (hsummgT 3).mul_left c3
            have hf4 : Summable f4 := (hsummgT 4).mul_left c4
            calc
              (∑' m : ℕ,
                (c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
                  + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m))
                  = ∑' m : ℕ, (f1 m + f2 m + (f3 m + f4 m)) := by
                    apply tsum_congr
                    intro m
                    simp [f1, f2, f3, f4]
                    ring
              _ = (∑' m, f1 m) + (∑' m, f2 m) + ((∑' m, f3 m) + (∑' m, f4 m)) := by
                    rw [← hf1.tsum_add hf2]
                    rw [← hf3.tsum_add hf4]
                    rw [← (hf1.add hf2).tsum_add (hf3.add hf4)]
              _ = c1 * (∑' m, assemblyGTail n M 1 m)
                  + c2 * (∑' m, assemblyGTail n M 2 m)
                  + c3 * (∑' m, assemblyGTail n M 3 m)
                  + c4 * (∑' m, assemblyGTail n M 4 m) := by
                    simp [f1, f2, f3, f4, tsum_mul_left]
                    ring
  have hTk : ∀ k, (∑' m, assemblyGTail n M k m)
      ≤ Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ)) *
          sigmaMoment k (massLam / Real.sqrt (n : ℝ) / 2) := by
    intro k
    rw [assemblyGTail_eq_bare]
    exact assembly_sigma_geom_tail_le k htp M
  have hE : Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ))
      ≤ Real.exp (-(massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hM_ge : ((M : ℝ)) ≥ (n : ℝ) ^ (2 / 3 : ℝ) - 1 := by
      have := Nat.lt_floor_add_one ((n : ℝ) ^ (2 / 3 : ℝ))
      rw [← hMdef] at this
      linarith
    have hn23ge2 : (2 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
      have hx0 : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hcube : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hnpos.le,
          show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      have hge : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
        nlinarith [h8]
      nlinarith [hcube, hge, hx0, mul_nonneg hx0 hx0,
        sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ) - 2),
        sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ) + 1)]
    have hMhalf : (1 / 2 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (M : ℝ) := by
      nlinarith [hM_ge, hn23ge2]
    have hsqrt_rpow : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsplitpow : (n : ℝ) ^ (2 / 3 : ℝ)
        = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hkey : (massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)
        ≤ massLam / Real.sqrt (n : ℝ) / 2 * (M : ℝ) := by
      rw [hsqrt_rpow]
      have hpos12 : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      calc
        (massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)
            = massLam / (n : ℝ) ^ (1 / 2 : ℝ) / 2 *
                ((1 / 2 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) := by
              rw [hsplitpow]
              field_simp
              ring
        _ ≤ massLam / (n : ℝ) ^ (1 / 2 : ℝ) / 2 * (M : ℝ) := by
              exact mul_le_mul_of_nonneg_left hMhalf (by positivity)
    nlinarith [hkey]
  have hsharp1 := hK1 _ ht2pos ht2le1
  have hsharp2 := hK2 _ ht2pos ht2le1
  have hsharp3 := hK3 _ ht2pos ht2le1
  have hsharp4 := hK4 _ ht2pos ht2le1
  have hp3 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 3
      = massLam ^ 3 / (8 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp4 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 4
      = massLam ^ 4 / (16 * (n : ℝ) ^ 2) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp5 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 5
      = massLam ^ 5 / (32 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp6 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 6
      = massLam ^ 6 / (64 * (n : ℝ) ^ 3) := by
    have hs6 : Real.sqrt (n : ℝ) ^ 6 = (n : ℝ) ^ 3 := by
      rw [show Real.sqrt (n : ℝ) ^ 6 = (Real.sqrt (n : ℝ) ^ 2) ^ 3 by ring, hs2]
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    rw [hs6]
    ring
  set E : ℝ := Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hsqle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [hs2, hs1, mul_nonneg hs0.le (sub_nonneg.mpr hs1)]
  have hinv_sqrt_le_one : 1 / Real.sqrt (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hs0]
    nlinarith
  have hinv_n_le_one : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have e1 : c1 * (∑' m, assemblyGTail n M 1 m) ≤ E * (12 * K1 / massLam ^ 3) := by
    calc
      c1 * (∑' m, assemblyGTail n M 1 m)
          ≤ c1 * (E * sigmaMoment 1 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 1) (by dsimp [c1]; positivity)
      _ ≤ c1 * (E * (K1 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp1 hEpos.le)
              (by dsimp [c1]; positivity)
      _ = E * (12 * K1 / massLam ^ 3) := by
            rw [hp3]
            dsimp [c1]
            field_simp
            ring
  have e2 : c2 * (∑' m, assemblyGTail n M 2 m) ≤ E * (30 * K2 / massLam ^ 4) := by
    calc
      c2 * (∑' m, assemblyGTail n M 2 m)
          ≤ c2 * (E * sigmaMoment 2 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 2) (by dsimp [c2]; positivity)
      _ ≤ c2 * (E * (K2 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp2 hEpos.le)
              (by dsimp [c2]; positivity)
      _ = E * (30 * K2 / (massLam ^ 4 * Real.sqrt (n : ℝ))) := by
            rw [hp4]
            dsimp [c2]
            field_simp
            ring
      _ ≤ E * (30 * K2 / massLam ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            calc
              30 * K2 / (massLam ^ 4 * Real.sqrt (n : ℝ))
                  = (30 * K2 / massLam ^ 4) * (1 / Real.sqrt (n : ℝ)) := by
                    field_simp [hs0.ne', hlam0.ne']
              _ ≤ (30 * K2 / massLam ^ 4) * 1 := by
                    exact mul_le_mul_of_nonneg_left hinv_sqrt_le_one (by positivity)
              _ = 30 * K2 / massLam ^ 4 := by ring
  have e3 : c3 * (∑' m, assemblyGTail n M 3 m)
      ≤ E * ((12 + 6 * C) * K3 / massLam ^ 5) := by
    calc
      c3 * (∑' m, assemblyGTail n M 3 m)
          ≤ c3 * (E * sigmaMoment 3 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 3) (by dsimp [c3]; have := C_pos; positivity)
      _ ≤ c3 * (E * (K3 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 5)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp3 hEpos.le)
              (by dsimp [c3]; have := C_pos; positivity)
      _ = E * (12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
            + 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))) := by
            rw [hp5]
            dsimp [c3]
            have hs3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
              rw [show Real.sqrt (n : ℝ) ^ 3 = Real.sqrt (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) by ring,
                hs2]
            field_simp [hs0.ne', hlam0.ne']
            rw [hs3]
            ring_nf
      _ ≤ E * ((12 + 6 * C) * K3 / massLam ^ 5) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            have hden1 : 12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                ≤ 12 * K3 / massLam ^ 5 := by
              calc
                12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                    = (12 * K3 / massLam ^ 5) *
                        ((1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) := by
                      field_simp [hs0.ne', hlam0.ne']
                _ ≤ (12 * K3 / massLam ^ 5) * 1 := by
                      have hprod_inv : (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) ≤ 1 := by
                        nlinarith [hinv_sqrt_le_one,
                          div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hs0.le]
                      exact mul_le_mul_of_nonneg_left hprod_inv (by positivity)
                _ = 12 * K3 / massLam ^ 5 := by ring
            have hden2 : 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                ≤ 6 * C * K3 / massLam ^ 5 := by
              calc
                6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                    = (6 * C * K3 / massLam ^ 5) * (1 / Real.sqrt (n : ℝ)) := by
                      field_simp [hs0.ne', hlam0.ne']
                _ ≤ (6 * C * K3 / massLam ^ 5) * 1 := by
                      exact mul_le_mul_of_nonneg_left hinv_sqrt_le_one (by positivity)
                _ = 6 * C * K3 / massLam ^ 5 := by ring
            calc
              12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                  + 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                  ≤ 12 * K3 / massLam ^ 5 + 6 * C * K3 / massLam ^ 5 := by
                    linarith
              _ = (12 + 6 * C) * K3 / massLam ^ 5 := by ring
  have e4 : c4 * (∑' m, assemblyGTail n M 4 m) ≤ E * (3 * C * K4 / massLam ^ 6) := by
    calc
      c4 * (∑' m, assemblyGTail n M 4 m)
          ≤ c4 * (E * sigmaMoment 4 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 4) (by dsimp [c4]; have := C_pos; positivity)
      _ ≤ c4 * (E * (K4 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 6)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp4 hEpos.le)
              (by dsimp [c4]; have := C_pos; positivity)
      _ = E * (3 * C * K4 / (massLam ^ 6 * (n : ℝ))) := by
            rw [hp6]
            dsimp [c4]
            field_simp [hnpos.ne', hlam0.ne']
      _ ≤ E * (3 * C * K4 / massLam ^ 6) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            calc
              3 * C * K4 / (massLam ^ 6 * (n : ℝ))
                  = (3 * C * K4 / massLam ^ 6) * (1 / (n : ℝ)) := by
                    field_simp [hnpos.ne', hlam0.ne']
              _ ≤ (3 * C * K4 / massLam ^ 6) * 1 := by
                    exact mul_le_mul_of_nonneg_left hinv_n_le_one (by positivity)
              _ = 3 * C * K4 / massLam ^ 6 := by ring
  calc
    (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := hsplit
    _ ≤ E * (12 * K1 / massLam ^ 3) + E * (30 * K2 / massLam ^ 4)
          + E * ((12 + 6 * C) * K3 / massLam ^ 5)
          + E * (3 * C * K4 / massLam ^ 6) := by
        linarith [e1, e2, e3, e4]
    _ = E * B := by
        rw [hBdef]
        ring
    _ ≤ Real.exp (-(massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)) * B := by
        exact mul_le_mul_of_nonneg_right hE hBnn
    _ ≤ (1 / (n : ℝ)) * B := by
        apply mul_le_mul_of_nonneg_right _ hBnn
        have hp := hpoly
        rw [pow_zero, one_mul] at hp
        exact hp
    _ = B / (n : ℝ) := by ring
    _ ≤ (B + 1) / (n : ℝ) := by
        rw [show (B + 1) / (n : ℝ) = B / (n : ℝ) + 1 / (n : ℝ) by ring]
        exact le_add_of_nonneg_right (by positivity)
