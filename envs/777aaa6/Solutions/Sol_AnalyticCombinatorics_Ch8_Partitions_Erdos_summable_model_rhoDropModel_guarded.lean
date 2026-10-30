-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_model_rhoDropModel_guarded
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:18.008875+00:00
-- url     : https://prove2.me/submissions/e4182842-f5aa-45b0-b191-5651115bcd3c

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_assembly_abs_add_three_le
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
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n : ℝ) := div_pos massLam_pos hs0
  let g : ℕ → ℕ → ℝ := fun k m =>
    if m = 0 then (0 : ℝ) else
      (m : ℝ) ^ k * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))
  have hgs (k : ℕ) : Summable (g k) := by
    dsimp [g]
    exact assembly_summable_sigma_exp k ht0
  let c1 : ℝ := 3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))
  let c2 : ℝ := 15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))
  let c3 : ℝ := 3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
    + 3 * C / (16 * (n : ℝ) ^ 3)
  let c4 : ℝ := 3 * C / (64 * (n : ℝ) ^ 4)
  have hdom : Summable (fun m : ℕ => c1 * g 1 m + c2 * g 2 m + c3 * g 3 m + c4 * g 4 m) := by
    refine (((hgs 1).mul_left c1).add ((hgs 2).mul_left c2)).add
      ((hgs 3).mul_left c3) |>.add ((hgs 4).mul_left c4) |>.congr ?_
    intro m
    ring
  have hnorm : Summable (fun m : ℕ =>
      ‖(if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hdom
    rw [Real.norm_eq_abs]
    rcases eq_or_ne m 0 with hm | hm
    · subst hm
      simp [g, c1, c2, c3, c4]
    · rw [if_neg hm]
      simpa [g, c1, c2, c3, c4] using model_product_abs_le n m
  exact summable_norm_iff.mp hnorm
