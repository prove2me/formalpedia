-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.main_model_rho_error_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:24:05.676028+00:00
-- url     : https://prove2.me/submissions/af210f13-2efc-428a-acc0-d251c4ee3cd4

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_le_power_sharp
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
# Mass-rate campaign: second-order kernel expansions (R8 §3.2–3.3)

Second-order expansions of the square-root drop and the reciprocal, with explicit
error constants:

* `sqrt_drop_second_order` — `|（√n−√(n−m)) − (m/(2s) + m²/(8s³))| ≤ m³/s⁵` for `m ≤ n`,
  via the purely algebraic identity `8s³E = (s−q)³(q+3s)` (`s=√n`, `q=√(n−m)`,
  `linear_combination` on `q² = s²−m`) — no calculus, no smallness hypothesis;
* `inv_sub_second_order` — `|1/(n−m) − (1/n + m/n²)| = m²/(n²(n−m)) ≤ 2m²/n³` for `2m ≤ n`.

Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Square-root drop, second order**: for `m ≤ n`, `1 ≤ n`,

  `|（√n − √(n−m)) − (m/(2√n) + m²/(8√n³))| ≤ m³/√n⁵`.
-/
lemma sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- the key polynomial identity: 8s⁴ − 8s³q − 4s²m − m² = (s−q)³(q+3s)
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  -- the expression E in closed form
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  -- nonnegativity and the bound
  have hsq_nonneg : 0 ≤ s - q := by linarith
  have hE_nonneg : 0 ≤ (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    have h1 : 0 ≤ (s - q) ^ 3 := by positivity
    have h2 : 0 ≤ q + 3 * s := by linarith
    positivity
  rw [hE_eq, abs_of_nonneg hE_nonneg]
  -- (s−q)(s+q) = m so s−q ≤ m/s; q+3s ≤ 4s
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [this, hq2]
    ring
  have hsq_le : s - q ≤ (m : ℝ) / s := by
    rw [le_div_iff₀ hs]
    calc (s - q) * s ≤ (s - q) * (s + q) :=
          mul_le_mul_of_nonneg_left (by linarith) hsq_nonneg
      _ = (m : ℝ) := hprod
  have hq3s : q + 3 * s ≤ 4 * s := by linarith
  calc (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3)
      ≤ ((m : ℝ) / s) ^ 3 * (4 * s) / (8 * s ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul _ hq3s (by linarith) (by positivity)
        exact pow_le_pow_left₀ hsq_nonneg hsq_le 3
    _ = (m : ℝ) ^ 3 / (2 * s ^ 5) := by
        field_simp
        ring
    _ ≤ (m : ℝ) ^ 3 / s ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hs 5]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Numerator model: the second-order `ρ`-drop and its error

The drift numerator is `muNum n = ∑_m erdosWeight n m · rhoDrop n m` with
`rhoDrop n m = 3(√n − √(n−m))`.  Its model replaces the `√`-drop by its two-term Taylor
expansion (`sqrt_drop_second_order`):

  `rhoDropModel n m = 3( m/(2√n) + m²/(8(√n)³) )`,   `|rhoDrop − rhoDropModel| ≤ 3 m³/(√n)⁵`.

This is the `ρ`-drop half of the `muNum` expansion (the kernel half is the banked `modelSummand`).
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **ρ-drop model error**: `|rhoDrop n m − rhoDropModel n m| ≤ 3 m³/(√n)⁵`. -/
lemma rhoDrop_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |rhoDrop n m - rhoDropModel n m| ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hkey := sqrt_drop_second_order hn hm
  have heq : rhoDrop n m - rhoDropModel n m
      = 3 * ((Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
          - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
            + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))) := by
    rw [rhoDrop, rhoDropModel]; ring
  rw [heq, abs_mul, show |(3 : ℝ)| = 3 from by norm_num]
  have : 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 = 3 * ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5) := by
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hkey (by norm_num)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Second cross error for the `muNum` two-term expansion

`∑_{1≤m≤⌊n^{2/3}⌋} |modelSummand n m| · |rhoDrop n m − rhoDropModel n m| ≤ K/n`.

The `modelSummand·(rhoDrop − rhoDropModel)` cross term: the `modelSummand` magnitude
(`|modelSummand| ≤ (1/n)g₀ + (1/n²)g₁ + (C/(8n²√n))g₂`) times the second-order `ρ`-drop error
(`|rhoDrop − rhoDropModel| ≤ 3m³/(√n)⁵`, `rhoDrop_sub_model_le`), expanded into the three shifted
Lambert moments `M₃,M₄,M₅` and bounded by `sigmaMoment_le_power_sharp`.  Sibling of
`main_kernel_error_rhoModel_le`, one fewer kernel factor.  Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Summability of the guarded Lambert summand `m^r σ(m) e^{−tm}` (`t>0`). -/
private lemma mre_summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [Sigma.sigmaR]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]

/-- `|modelSummand|` magnitude bound (triangle inequality on its three terms). -/
private lemma mre_abs_modelSummand_le (n m : ℕ) :
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

/-- `|rhoDrop − rhoDropModel|` magnitude (from `rhoDrop_sub_model_le`, abs form). -/
private lemma mre_abs_rhoDrop_sub_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |rhoDrop n m - rhoDropModel n m| ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 :=
  rhoDrop_sub_model_le hn hm

/-- The three-moment bound for the second cross error. -/
private theorem mre_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ)))
        ≤ K / (n:ℝ) := by
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  obtain ⟨K5, hK5nn, hK5⟩ := sigmaMoment_le_power_sharp 5
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := by simpa [hlamdef] using massLam_pos
  set B : ℝ := 3 * K3 / lam ^ 5 + 3 * K4 / lam ^ 6 + 3 * C * K5 / (8 * lam ^ 7) with hBdef
  refine ⟨B + 1, by have := C_pos; positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    refine ⟨by exact_mod_cast (le_trans (le_max_left _ _) hn), ?_⟩
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (le_max_right _ _) hn))
  filter_upwards [hev] with n hn
  obtain ⟨hn1r, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hn1r
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hspos : 0 < s := by simpa [hsdef] using hs0
  have hs1' : 1 ≤ s := by simpa [hsdef] using hs1
  have hs2 : s ^ 2 = (n:ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hspos, ← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  have hM3 := hK3 t ht0 ht1
  have hM4 := hK4 t ht0 ht1
  have hM5 := hK5 t ht0 ht1
  have hden_ns : (n:ℝ) ≤ (n:ℝ) * s := by nlinarith [hnpos, hs1']
  have c4_nonneg : 0 ≤ 3 * K4 / lam ^ 6 := by positivity
  have c5_nonneg : 0 ≤ 3 * C * K5 / (8 * lam ^ 7) := by
    have := C_pos; positivity
  have b3 :
      (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t ≤ (3 * K3 / lam ^ 5) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / ((n:ℝ) ^ 3 * s) := by positivity
    calc (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        ≤ (3 / ((n:ℝ) ^ 3 * s)) * (K3 / t ^ 5) := mul_le_mul_of_nonneg_left hM3 hcoef
      _ = (3 * K3 / lam ^ 5) / (n:ℝ) := by rw [htdef, ← hs2]; field_simp
  have b4 :
      (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t ≤ (3 * K4 / lam ^ 6) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / ((n:ℝ) ^ 4 * s) := by positivity
    calc (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t
        ≤ (3 / ((n:ℝ) ^ 4 * s)) * (K4 / t ^ 6) := mul_le_mul_of_nonneg_left hM4 hcoef
      _ = (3 * K4 / lam ^ 6) / ((n:ℝ) * s) := by rw [htdef, ← hs2]; field_simp
      _ ≤ (3 * K4 / lam ^ 6) / (n:ℝ) := div_le_div_of_nonneg_left c4_nonneg hnpos hden_ns
  have b5 :
      (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t ≤ (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := by
    have hCpos := C_pos
    have hcoef : 0 ≤ 3 * C / (8 * (n:ℝ) ^ 5) := by positivity
    calc (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t
        ≤ (3 * C / (8 * (n:ℝ) ^ 5)) * (K5 / t ^ 7) := mul_le_mul_of_nonneg_left hM5 hcoef
      _ = (3 * C * K5 / (8 * lam ^ 7)) / ((n:ℝ) * s) := by rw [htdef, ← hs2]; field_simp
      _ ≤ (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := div_le_div_of_nonneg_left c5_nonneg hnpos hden_ns
  have hsum :
      (3 * K3 / lam ^ 5) / (n:ℝ) + (3 * K4 / lam ^ 6) / (n:ℝ)
        + (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) = B / (n:ℝ) := by
    rw [hBdef]; ring
  calc
    (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
      = (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        + (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t := by rw [hsdef, htdef, hlamdef]
    _ ≤ (3 * K3 / lam ^ 5) / (n:ℝ) + (3 * K4 / lam ^ 6) / (n:ℝ)
          + (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := by linarith [b3, b4, b5]
    _ = B / (n:ℝ) := hsum
    _ ≤ (B + 1) / (n:ℝ) := by
        rw [show (B + 1) / (n:ℝ) = B / (n:ℝ) + 1 / (n:ℝ) by ring]
        exact le_add_of_nonneg_right (by positivity)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000
open Filter Finset
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
        |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n:ℝ) := by
  obtain ⟨K, hKpos, hKbound⟩ := mre_moment_bound
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hKbound, Filter.eventually_ge_atTop 1] with n hKb hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hM
  have hMn : M ≤ n := by
    rw [hM]
    have hle : (n:ℝ) ^ (2/3 : ℝ) ≤ (n:ℝ) := by
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      calc (n:ℝ) ^ (2/3 : ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (n:ℝ) := by rw [Real.rpow_one]
    calc ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ ≤ ⌊(n:ℝ)⌋₊ := Nat.floor_mono hle
      _ = n := Nat.floor_natCast n
  -- step 1: pointwise bound  |modelSummand|·|drop-err| ≤ (abs bound)·(3m³/√n⁵)
  have hstep1 :
      (∑ m ∈ Finset.Icc 1 M, |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ ∑ m ∈ Finset.Icc 1 M,
          (((1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
            + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
          * (3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmle⟩ := hm
    have hmn : m ≤ n := le_trans hmle hMn
    have habs := mre_abs_modelSummand_le n m
    have hrho := mre_abs_rhoDrop_sub_le hn1 hmn
    exact mul_le_mul habs hrho (abs_nonneg _) (le_trans (abs_nonneg _) habs)
  -- step 2: rearrange each summand into the three moment summands
  have hrw : ∀ m : ℕ,
      (((1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      * (3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5))
      = (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 5 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
    intro m
    rcases eq_or_ne m 0 with h | h
    · subst h; simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h]
      set s := Real.sqrt (n:ℝ) with hsd
      have hs2 : s ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
      have hsne : s ≠ 0 := by rw [hsd]; exact hs0.ne'
      rw [← hs2]
      field_simp
  rw [Finset.sum_congr rfl (fun m _ => hrw m), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hstep1
  -- step 3: each finite divisor sum ≤ the full Lambert moment
  have hfin : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 M,
        (if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ sigmaMoment r (massLam / Real.sqrt (n:ℝ)) := by
    intro r
    have hge0 : ∀ k : ℕ, 0 ≤
        (if k = 0 then (0:ℝ) else (k:ℝ) ^ r * Sigma.sigmaR k * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (k:ℝ))) := by
      intro k
      rcases eq_or_ne k 0 with h | h
      · simp [h]
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg k)) (Real.exp_pos _).le
    have hsumm := mre_summable_sigma_exp r ht0
    have hle := sum_le_hasSum (Finset.Icc 1 M) (fun k _ => hge0 k) hsumm.hasSum
    rw [sigmaMoment]
    refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro m _; rfl
  -- step 4: combine
  have hmono :
      (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 5 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ)) := by
    have hC := C_pos
    gcongr <;> [exact hfin 3; exact hfin 4; exact hfin 5]
  exact le_trans hstep1 (le_trans hmono hKb)
