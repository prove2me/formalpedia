-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.model_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:04.227257+00:00
-- url     : https://prove2.me/submissions/7e84dae5-e925-4fb6-825e-8b1605229b82

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
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

private lemma sigmaR_zero : Sigma.sigmaR 0 = 0 := by
  simp [Sigma.sigmaR]

/-- Summability of the (sign-adjusted) Lambert summand `m^r σ(m) e^{−tm}` for `t > 0`. -/
private lemma summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [sigmaR_zero]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]

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

/-- Geometric tail-extraction: for `t > 0`, the `m > M` tail of the Lambert summand `m^k σ(m) e^{−tm}`
is bounded by `e^{−(t/2)M}` times the full `(t/2)`-moment. (For `m ≥ M`, `e^{−tm} ≤ e^{−(t/2)M}e^{−(t/2)m}`.) -/
private lemma sigma_geom_tail_le (k : ℕ) {t : ℝ} (ht : 0 < t) (M : ℕ) :
    (∑' m : ℕ, (if m ≤ M then (0:ℝ)
        else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))))
      ≤ Real.exp (-(t/2) * (M:ℝ)) * sigmaMoment k (t/2) := by
  have ht2 : 0 < t/2 := by linarith
  have hg0 := summable_sigma_exp k ht
  have hg2 := summable_sigma_exp k ht2
  set f : ℕ → ℝ := fun m => if m ≤ M then (0:ℝ)
      else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ)) with hfdef
  set g'' : ℕ → ℝ := fun m => Real.exp (-(t/2) * (M:ℝ)) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) with hg''def
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m; rw [hfdef]; dsimp only; split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  have hfle0 : ∀ m, f m ≤ (if m = 0 then (0:ℝ)
      else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
    intro m; rw [hfdef]; dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]; split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
  have hfsumm : Summable f := Summable.of_nonneg_of_le hfnn hfle0 hg0
  have hg''summ : Summable g'' := hg2.mul_left _
  have hbound : ∀ m, f m ≤ g'' m := by
    intro m; rw [hfdef, hg''def]; dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      apply mul_nonneg (Real.exp_pos _).le
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
      have hexp : Real.exp (-t * (m:ℝ))
          ≤ Real.exp (-(t/2) * (M:ℝ)) * Real.exp (-(t/2) * (m:ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmM : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast h.le
        nlinarith [hmM, ht]
      calc (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))
          ≤ (m:ℝ) ^ k * Sigma.sigmaR m * (Real.exp (-(t/2) * (M:ℝ)) * Real.exp (-(t/2) * (m:ℝ))) :=
            mul_le_mul_of_nonneg_left hexp
              (mul_nonneg (by positivity) (sigmaR_nonneg m))
        _ = Real.exp (-(t/2) * (M:ℝ)) *
              ((m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) := by ring
  calc (∑' m, f m) ≤ ∑' m : ℕ, g'' m := Summable.tsum_le_tsum hbound hfsumm hg''summ
    _ = Real.exp (-(t/2) * (M:ℝ)) *
          ∑' m : ℕ, (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) :=
        tsum_mul_left
    _ = Real.exp (-(t/2) * (M:ℝ)) * sigmaMoment k (t/2) := by rw [sigmaMoment]

/-- Per-`m` majorant of `|modelSummand|`: triangle inequality on the coefficient gives the three
nonnegative Lambert pieces (`k=0,1,2`). -/
private lemma abs_modelSummand_le (n m : ℕ) :
    |modelSummand n m|
      ≤ (1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
  have hCpos : 0 < C := C_pos
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · rw [modelSummand, if_neg h, if_neg h, if_neg h, if_neg h]
    rw [abs_mul, abs_mul, abs_of_nonneg (sigmaR_nonneg m), abs_of_pos (Real.exp_pos _)]
    have hcoef : |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ 1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by
      have h1 : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
      have h2 : (0:ℝ) ≤ (m:ℝ) / (n:ℝ) ^ 2 := by positivity
      have h3 : (0:ℝ) ≤ C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by positivity
      rw [abs_le]; constructor <;> linarith
    calc Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            (1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg (sigmaR_nonneg m) (Real.exp_pos _).le)
      _ = _ := by ring

/-- Abbreviation: the `m > M` tail of the `k`-th Lambert summand at `t = massLam/√n`. -/
private def gTail (n M k m : ℕ) : ℝ :=
  if m ≤ M then (0:ℝ)
  else (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))

private lemma gTail_nonneg (n M k m : ℕ) : 0 ≤ gTail n M k m := by
  rw [gTail]; split
  · rfl
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le

private lemma summable_gTail (n M k : ℕ) {t : ℝ} (ht : massLam / Real.sqrt (n:ℝ) = t) (htp : 0 < t) :
    Summable (fun m => gTail n M k m) := by
  apply Summable.of_nonneg_of_le (gTail_nonneg n M k) (fun m => ?_) (summable_sigma_exp k htp)
  rw [gTail, ← ht]; split
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  · exact le_refl _

/-- `gTail` equals the bare-`else` tail used by `sigma_geom_tail_le` (the inner `if m=0` never fires
for `m > M`). -/
private lemma gTail_eq_bare (n M k : ℕ) :
    (∑' m : ℕ, gTail n M k m)
      = ∑' m : ℕ, (if m ≤ M then (0:ℝ)
          else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
  apply tsum_congr; intro m
  rw [gTail]
  rcases le_or_gt m M with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑' m : ℕ, (if m ≤ ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ then (0:ℝ) else |modelSummand n m|))
        ≤ K / (n:ℝ) := by
  obtain ⟨K0, hK0nn, hK0⟩ := sigmaMoment_le_power_sharp 0
  obtain ⟨K1, hK1nn, hK1⟩ := sigmaMoment_le_power_sharp 1
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  have hlam0 : 0 < massLam := massLam_pos
  have hCpos : 0 < C := C_pos
  set B : ℝ := 4 * K0 / massLam ^ 2 + 8 * K1 / massLam ^ 3 + 2 * C * K2 / massLam ^ 4 with hBdef
  have hBnn : 0 ≤ B := by
    have t0 : (0:ℝ) ≤ 4 * K0 / massLam ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hK0nn) (by positivity)
    have t1 : (0:ℝ) ≤ 8 * K1 / massLam ^ 3 :=
      div_nonneg (mul_nonneg (by norm_num) hK1nn) (by positivity)
    have t2 : (0:ℝ) ≤ 2 * C * K2 / massLam ^ 4 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hK2nn) (by positivity)
    rw [hBdef]; linarith
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sixthRoot_le_inv (massLam / 4) (by positivity) 0,
    Filter.eventually_ge_atTop (max 8 ⌈massLam ^ 2⌉₊)] with n hpoly hnge
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hnge
  have hnlamc : ⌈massLam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hnge
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnge1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hnge1
  have htp : 0 < massLam / Real.sqrt (n:ℝ) := div_pos hlam0 hs0
  have hlamle : massLam ≤ Real.sqrt (n:ℝ) := by
    calc massLam = Real.sqrt (massLam ^ 2) := (Real.sqrt_sq hlam0.le).symm
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt (by
          have : (⌈massLam ^ 2⌉₊ : ℝ) ≤ (n:ℝ) := by exact_mod_cast hnlamc
          linarith [Nat.le_ceil (massLam ^ 2)])
  have ht2pos : 0 < massLam / Real.sqrt (n:ℝ) / 2 := by positivity
  have ht2le1 : massLam / Real.sqrt (n:ℝ) / 2 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]; nlinarith [hlamle, hs1, hlam0]
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  -- step 1: model tail ≤ three weighted sigma-tails
  have hsummgT : ∀ k, Summable (fun m => gTail n M k m) := fun k => summable_gTail n M k rfl htp
  have hpt : ∀ m, (if m ≤ M then (0:ℝ) else |modelSummand n m|)
      ≤ (1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m := by
    intro m
    rcases le_or_gt m M with h | h
    · rw [if_pos h, gTail, gTail, gTail, if_pos h, if_pos h, if_pos h]; simp
    · rw [if_neg (not_le.mpr h), gTail, gTail, gTail,
        if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (not_le.mpr h)]
      exact abs_modelSummand_le n m
  have h3summ : Summable (fun m => (1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
      + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m) :=
    (((hsummgT 0).mul_left _).add ((hsummgT 1).mul_left _)).add ((hsummgT 2).mul_left _)
  have hsummF : Summable (fun m => if m ≤ M then (0:ℝ) else |modelSummand n m|) :=
    Summable.of_nonneg_of_le (fun m => by split <;> positivity) hpt h3summ
  have hsplit : (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
      ≤ (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := by
    calc (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
        ≤ ∑' m, ((1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m) :=
          Summable.tsum_le_tsum hpt hsummF h3summ
      _ = (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := by
          rw [(((hsummgT 0).mul_left _).add ((hsummgT 1).mul_left _)).tsum_add ((hsummgT 2).mul_left _),
            ((hsummgT 0).mul_left _).tsum_add ((hsummgT 1).mul_left _),
            tsum_mul_left, tsum_mul_left, tsum_mul_left]
  -- step 2: each sigma-tail ≤ E · M_k(t/2)
  have hTk : ∀ k, (∑' m, gTail n M k m)
      ≤ Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ)) *
          sigmaMoment k (massLam / Real.sqrt (n:ℝ) / 2) := by
    intro k; rw [gTail_eq_bare]; exact sigma_geom_tail_le k htp M
  -- step 3: bound everything by B · E, then E ≤ exp(−(λ/4) n^{1/6}), then poly.
  have hE : Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ))
      ≤ Real.exp (-(massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    -- (λ/4) n^{1/6} ≤ (t/2) M
    have hM_ge : ((M:ℝ)) ≥ (n:ℝ) ^ (2/3 : ℝ) - 1 := by
      have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ))
      rw [hMdef]; linarith
    have hn23ge2 : (2:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := by
      have hx0 : 0 ≤ (n:ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hcube : ((n:ℝ) ^ (2/3 : ℝ)) ^ 3 = (n:ℝ) ^ 2 := by
        rw [← Real.rpow_natCast ((n:ℝ) ^ (2/3 : ℝ)) 3, ← Real.rpow_mul hnpos.le,
          show (2/3 : ℝ) * ((3:ℕ):ℝ) = ((2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
      have hge : (64:ℝ) ≤ (n:ℝ) ^ 2 := by
        have h8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
        nlinarith [h8]
      nlinarith [hcube, hge, hx0, mul_nonneg hx0 hx0, sq_nonneg ((n:ℝ) ^ (2/3 : ℝ) - 2),
        sq_nonneg ((n:ℝ) ^ (2/3 : ℝ) + 1)]
    -- M ≥ (1/2) n^{2/3}
    have hMhalf : (1/2 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) ≤ (M:ℝ) := by nlinarith [hM_ge, hn23ge2]
    -- (t/2)·M = (λ/(2√n))·M ≥ (λ/(2√n))·(1/2)n^{2/3} = (λ/4) n^{1/6}
    have hsqrt_rpow : Real.sqrt (n:ℝ) = (n:ℝ) ^ (1/2 : ℝ) := Real.sqrt_eq_rpow _
    have hsplitpow : (n:ℝ) ^ (2/3 : ℝ) = (n:ℝ) ^ (1/2 : ℝ) * (n:ℝ) ^ (1/6 : ℝ) := by
      rw [← Real.rpow_add hnpos]; norm_num
    have hkey : (massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)
        ≤ massLam / Real.sqrt (n:ℝ) / 2 * (M:ℝ) := by
      rw [hsqrt_rpow]
      have hpos16 : (0:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hpos12 : (0:ℝ) < (n:ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      calc (massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)
          = massLam / (n:ℝ) ^ (1/2 : ℝ) / 2 * ((1/2 : ℝ) * (n:ℝ) ^ (2/3 : ℝ)) := by
            rw [hsplitpow]; field_simp; ring
        _ ≤ massLam / (n:ℝ) ^ (1/2 : ℝ) / 2 * (M:ℝ) := by
            apply mul_le_mul_of_nonneg_left hMhalf (by positivity)
    nlinarith [hkey]
  -- assemble: model tail ≤ B·E ≤ B·exp(−(λ/4)n^{1/6}) ≤ B/n ≤ (B+1)/n
  have hsharp0 := hK0 _ ht2pos ht2le1
  have hsharp1 := hK1 _ ht2pos ht2le1
  have hsharp2 := hK2 _ ht2pos ht2le1
  -- (t/2)-power identities
  have hp2 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 2 = massLam ^ 2 / (4 * (n:ℝ)) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  have hp3 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 3
      = massLam ^ 3 / (8 * (n:ℝ) * Real.sqrt (n:ℝ)) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  have hp4 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 4 = massLam ^ 4 / (16 * (n:ℝ) ^ 2) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  -- final assembly
  have hlamne : massLam ≠ 0 := hlam0.ne'
  have hnne : (n:ℝ) ≠ 0 := hnpos.ne'
  have hsne : Real.sqrt (n:ℝ) ≠ 0 := hs0.ne'
  set E : ℝ := Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hsqle : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
    nlinarith [hs2, hs1, mul_nonneg hs0.le (sub_nonneg.mpr hs1)]
  have e0 : (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) ≤ E * (4 * K0 / massLam ^ 2) := by
    calc (1 / (n:ℝ)) * (∑' m, gTail n M 0 m)
        ≤ (1 / (n:ℝ)) * (E * sigmaMoment 0 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 0) (by positivity)
      _ ≤ (1 / (n:ℝ)) * (E * (K0 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp0 hEpos.le) (by positivity)
      _ = E * (4 * K0 / massLam ^ 2) := by rw [hp2]; field_simp
  have e1 : (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m) ≤ E * (8 * K1 / massLam ^ 3) := by
    calc (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        ≤ (1 / (n:ℝ) ^ 2) * (E * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 1) (by positivity)
      _ ≤ (1 / (n:ℝ) ^ 2) * (E * (K1 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp1 hEpos.le) (by positivity)
      _ = E * (8 * K1 * Real.sqrt (n:ℝ) / (massLam ^ 3 * (n:ℝ))) := by rw [hp3]; field_simp
      _ ≤ E * (8 * K1 / massLam ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hEpos.le
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsqle, hK1nn, hlam0, pow_pos hlam0 3,
            mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK1nn) (pow_nonneg hlam0.le 3)]
  have e2 : (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m)
      ≤ E * (2 * C * K2 / massLam ^ 4) := by
    calc (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m)
        ≤ (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
            (E * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 2) (by positivity)
      _ ≤ (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
            (E * (K2 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp2 hEpos.le) (by positivity)
      _ = E * (2 * C * K2 / (massLam ^ 4 * Real.sqrt (n:ℝ))) := by rw [hp4]; field_simp; ring
      _ ≤ E * (2 * C * K2 / massLam ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ hEpos.le
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hs1, hK2nn, hlam0, hCpos, pow_pos hlam0 4,
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCpos.le) hK2nn)
              (pow_nonneg hlam0.le 4)]
  calc (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
      ≤ (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := hsplit
    _ ≤ E * (4 * K0 / massLam ^ 2) + E * (8 * K1 / massLam ^ 3) + E * (2 * C * K2 / massLam ^ 4) := by
        linarith [e0, e1, e2]
    _ = E * B := by rw [hBdef]; ring
    _ ≤ Real.exp (-(massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)) * B :=
        mul_le_mul_of_nonneg_right hE hBnn
    _ ≤ (1 / (n:ℝ)) * B := by
        apply mul_le_mul_of_nonneg_right _ hBnn
        have hp := hpoly; rw [pow_zero, one_mul] at hp; exact hp
    _ = B / (n:ℝ) := by ring
    _ ≤ (B + 1) / (n:ℝ) := by
        have hsplit2 : (B + 1) / (n:ℝ) = B / (n:ℝ) + 1 / (n:ℝ) := by ring
        have h1n : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
        rw [hsplit2]; linarith
