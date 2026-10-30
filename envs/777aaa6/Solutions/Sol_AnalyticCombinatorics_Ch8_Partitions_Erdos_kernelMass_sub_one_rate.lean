-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_sub_one_rate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:16:20.151991+00:00
-- url     : https://prove2.me/submissions/f8f5632d-540c-4cec-b48f-c3fc65196afc

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateAssembly
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_boseReg0Deriv_bdd_near_zero
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_approx2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_sq
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_two_asymp_weak
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
# Mass-rate campaign: Lambert moments — definitions and the central cancellation (R8)

The critical-path brick `|kernelMass n − 1| = O(1/n)` goes through smoothed Lambert
moments `M_r(t) = Σ_m m^r σ(m) e^{−tm}` (NOT a refined pointwise summatory, which cannot
have an `o(x)` secondary at integers because of the `σ(n)` jumps).  This file banks the
definitions, the saddle parameter `λ = C/2` with `λ² = π²/6`, the Bose kernel with its
regularization, and the central algebraic cancellation of the `n^{−1/2}` coefficients:

  `−1/(2λ) + 2Z/λ³ − (C/8)·6Z/λ⁴ = 0`  (`Z = λ²`, `C = 2λ`).

Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The Bose kernel `e^{−x}/(1−e^{−x})²`. -/
noncomputable def boseKernel (x : ℝ) : ℝ :=
  Real.exp (-x) / (1 - Real.exp (-x)) ^ 2

/-- The regularized Bose kernel `boseKernel x − 1/x²` (extends continuously to `−1/12` at 0). -/
noncomputable def boseReg0 (x : ℝ) : ℝ :=
  boseKernel x - 1 / x ^ 2

/-- The Bose kernel is the derivative of `−1/(e^x−1)`: closed antiderivative identity. -/
lemma boseKernel_eq_exp_form {x : ℝ} (hx : 0 < x) :
    boseKernel x = Real.exp x / (Real.exp x - 1) ^ 2 := by
  rw [boseKernel]
  have hexp : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg]
    exact inv_eq_one_div _
  have hepos : 0 < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := hepos.ne'
  rw [hexp]
  rw [div_eq_div_iff]
  · field_simp
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < 1 - 1 / Real.exp x := by
      rw [sub_pos, div_lt_one hepos]
      exact h1
    positivity
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < Real.exp x - 1 := by linarith
    positivity

/--
**The central cancellation** (R8 §6): the three `n^{−1/2}` coefficients — the `−1/(2t)`
secondary of `M₀`, the reciprocal correction through `M₁`, and the exponent correction
through `M₂` — cancel exactly at the saddle `t = λ/√n`.
-/
lemma mass_rate_sqrt_coeff_cancel :
    -(1 / (2 * massLam)) + 2 * (Real.pi ^ 2 / 6) / massLam ^ 3
      - C * (6 * (Real.pi ^ 2 / 6)) / (8 * massLam ^ 4) = 0 := by
  have hlam := massLam_pos
  have hC : C = 2 * massLam := by
    rw [massLam]
    ring
  rw [hC, ← massLam_sq]
  field_simp
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
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

/-- Drop-the-zero bridge: `Σ'_{m:ℕ} [m≠0]·f m = Σ'_{c:ℕ+} f c` (no summability needed). -/
lemma tsum_if_ne_zero_eq_pnat (f : ℕ → ℝ) :
    ∑' m : ℕ, (if m = 0 then 0 else f m) = ∑' c : ℕ+, f (c : ℕ) := by
  have hinj : Function.Injective (fun c : ℕ+ => (c : ℕ)) :=
    fun a b h => PNat.coe_injective h
  have hsupp : Function.support (fun m : ℕ => if m = 0 then 0 else f m)
      ⊆ Set.range (fun c : ℕ+ => (c : ℕ)) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx0 : x ≠ 0 := by
      intro h0
      apply hx
      rw [h0, if_pos rfl]
    exact ⟨⟨x, Nat.pos_of_ne_zero hx0⟩, rfl⟩
  have h := hinj.tsum_eq hsupp
  rw [← h]
  refine tsum_congr fun c => ?_
  rw [if_neg (PNat.ne_zero c)]

/-- The inner geometric-derivative sum: `Σ'_{c:ℕ+} c·y^c = y/(1−y)²` for `‖y‖ < 1`. -/
lemma tsum_pnat_coe_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' c : ℕ+, ((c : ℕ) : ℝ) * y ^ (c : ℕ) = y / (1 - y) ^ 2 := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) * y ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hy).summable
  have hbase : ∑' n : ℕ, (n : ℝ) * y ^ n = y / (1 - y) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hy
  have hshift := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℝ) * y ^ n)
  rw [hshift]
  have hzero := hsum.tsum_eq_zero_add
  rw [← hbase, hzero]
  simp

/--
**The Lambert identity for `M₀`** (R8 §2.1):

  `Σ_m σ(m)e^{−tm} = Σ_k e^{−tk}/(1−e^{−tk})²`.
-/
theorem sigmaMoment_zero_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 0 t = ∑' k : ℕ, if k = 0 then 0 else boseKernel (t * (k : ℝ)) := by
  set r : ℝ := Real.exp (-t) with hrdef
  have hr : ‖r‖ < 1 := by
    rw [hrdef, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hrm : ∀ m : ℕ, Real.exp (-t * (m : ℝ)) = r ^ m := by
    intro m
    rw [hrdef, ← Real.exp_nat_mul]
    congr 1
    ring
  -- LHS in ℕ+ σ-form
  have hL : sigmaMoment 0 t
      = ∑' e : ℕ+, ((ArithmeticFunction.sigma 1 (e : ℕ) : ℕ) : ℝ) * r ^ (e : ℕ) := by
    rw [sigmaMoment, tsum_if_ne_zero_eq_pnat
      (f := fun m : ℕ => (m : ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))]
    refine tsum_congr fun e => ?_
    rw [pow_zero, one_mul, hrm, sigmaR_eq_sigma_one]
  -- RHS in ℕ+ Bose form
  have hR : (∑' k : ℕ, if k = 0 then 0 else boseKernel (t * (k : ℝ)))
      = ∑' d : ℕ+, boseKernel (t * ((d : ℕ) : ℝ)) :=
    tsum_if_ne_zero_eq_pnat (f := fun k : ℕ => boseKernel (t * (k : ℝ)))
  rw [hL, hR]
  -- each Bose term is the inner geometric-derivative sum
  have hinner : ∀ d : ℕ+, boseKernel (t * ((d : ℕ) : ℝ))
      = ∑' c : ℕ+, ((c : ℕ) : ℝ) * r ^ ((d : ℕ) * (c : ℕ)) := by
    intro d
    have hyd : ‖r ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg r) hr (PNat.ne_zero d)
    have hexp_eq : Real.exp (-(t * ((d : ℕ) : ℝ))) = r ^ (d : ℕ) := by
      rw [show -(t * ((d : ℕ) : ℝ)) = -t * ((d : ℕ) : ℝ) by ring]
      exact hrm (d : ℕ)
    have h2 : boseKernel (t * ((d : ℕ) : ℝ)) = r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2 := by
      rw [boseKernel, hexp_eq]
    rw [h2, ← tsum_pnat_coe_mul_geometric hyd]
    refine tsum_congr fun c => ?_
    rw [pow_mul]
  rw [tsum_congr hinner]
  -- Mathlib's Lambert rearrangement at k = 1
  have hML := tsum_prod_pow_eq_tsum_sigma (𝕜 := ℝ) 1 hr
  rw [← hML]
  refine tsum_congr fun d => tsum_congr fun c => ?_
  push_cast
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: Basel-scaled sum and the kernel split (brick-22 prerequisites)

`Σ'_{k≥1} 1/(tk)² = (π²/6)/t²` and `boseKernel x = 1/x² + boseReg0 x`.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The kernel split (definitional). -/
lemma boseKernel_eq_inv_sq_add_reg (x : ℝ) :
    boseKernel x = 1 / x ^ 2 + boseReg0 x := by
  rw [boseReg0]
  ring

/-- Basel, in the `ℕ`-indexed guarded form: `Σ'_{k≥1} 1/k² = π²/6`. -/
lemma tsum_if_inv_sq :
    (∑' k : ℕ, if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) = Real.pi ^ 2 / 6 := by
  have hb := hasSum_zeta_two
  rw [← hb.tsum_eq]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]

/-- Basel scaled: `Σ'_{k≥1} 1/(tk)² = (π²/6)/t²` for `t ≠ 0`. -/
lemma tsum_if_inv_sq_scaled {t : ℝ} (ht : t ≠ 0) :
    (∑' k : ℕ, if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = (Real.pi ^ 2 / 6) / t ^ 2 := by
  have hfact : ∀ k : ℕ, (if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = (1 / t ^ 2) * (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [if_neg hk, if_neg hk]
      field_simp
  calc (∑' k : ℕ, if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = ∑' k : ℕ, (1 / t ^ 2) * (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) :=
        tsum_congr hfact
    _ = (1 / t ^ 2) * ∑' k : ℕ, (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) :=
        tsum_mul_left
    _ = (Real.pi ^ 2 / 6) / t ^ 2 := by
        rw [tsum_if_inv_sq]
        ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: polynomial exponential bounds (R10 bricks 1–3)

Two-sided polynomial bounds for `e^x − 1` on `[0,1]` from `Real.exp_bound` at orders 3, 4 —
the only exp-Taylor input the whole moment package needs.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Order-3 remainder: `|e^x − 1 − x − x²/2| ≤ x³` on `[0,1]`. -/
lemma exp_sub_one_sub_self_sq_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3 := by
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have h := Real.exp_bound habs (n := 3) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 3, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs3 : |x| ^ 3 = x ^ 3 := by
    rw [abs_of_nonneg hx0]
  rw [habs3] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2|
      = |Real.exp x - (1 + x + x ^ 2 / 2)| := by ring_nf
    _ ≤ x ^ 3 * ((3 : ℕ).succ / ((Nat.factorial 3 : ℝ) * 3)) := h
    _ ≤ x ^ 3 := by
        have hx3 : (0 : ℝ) ≤ x ^ 3 := by positivity
        have hc : ((3 : ℕ).succ : ℝ) / ((Nat.factorial 3 : ℝ) * 3) ≤ 1 := by
          norm_num [Nat.factorial]
        nlinarith [hx3, hc]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: boseReg0 bounds (R10 bricks 4–6)

The rational form of `boseReg0`, boundedness near zero (`|boseReg0| ≤ 4` on `(0,1]`, via
the exact numerator identity `x²eˣ − (eˣ−1)² = x⁴/4 − 2xδ − δ²` with `|δ| ≤ x³`), and the
tail bound `|boseReg0| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rational form of `boseReg0` over a common denominator. -/
lemma boseReg0_eq_small_num {x : ℝ} (hx : 0 < x) :
    boseReg0 x = (x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2) /
      (x ^ 2 * (Real.exp x - 1) ^ 2) := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  rw [boseReg0, boseKernel_eq_exp_form hx]
  field_simp

/-- `|boseReg0| ≤ 4` on `(0,1]`. -/
lemma boseReg0_bdd_near_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |boseReg0 x| ≤ 4 := by
  set δ : ℝ := Real.exp x - 1 - x - x ^ 2 / 2 with hδdef
  have hδ : |δ| ≤ x ^ 3 := by
    rw [hδdef]
    have := exp_sub_one_sub_self_sq_bound hx0.le hx1
    convert this using 2
  have hδlo := (abs_le.mp hδ).1
  have hδhi := (abs_le.mp hδ).2
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  -- exact numerator identity
  have hnum_eq : x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2
      = x ^ 4 / 4 - 2 * x * δ - δ ^ 2 := by
    rw [hδdef]
    ring
  have hx3 : x ^ 3 ≤ x ^ 2 := by nlinarith [hx0.le]
  have hnum_abs : |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| ≤ 4 * x ^ 4 := by
    rw [hnum_eq, abs_le]
    have hδsq : δ ^ 2 ≤ x ^ 6 := by nlinarith [hδlo, hδhi]
    have hx6 : x ^ 6 ≤ x ^ 4 := by nlinarith [hx0.le, hx1, pow_pos hx0 4]
    have hxδhi : x * δ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left hδhi hx0.le
    have hxδlo : x * (-(x ^ 3)) ≤ x * δ := mul_le_mul_of_nonneg_left hδlo hx0.le
    constructor
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6]
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6, sq_nonneg δ]
  have hsq : x ^ 2 ≤ (Real.exp x - 1) ^ 2 := by nlinarith [hy, hx0.le]
  have hden_ge : x ^ 4 ≤ x ^ 2 * (Real.exp x - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ x ^ 2)]
  have hden_pos : 0 < x ^ 2 * (Real.exp x - 1) ^ 2 := by positivity
  rw [boseReg0_eq_small_num hx0, abs_div,
    abs_of_pos hden_pos]
  calc |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| / (x ^ 2 * (Real.exp x - 1) ^ 2)
      ≤ (4 * x ^ 4) / x ^ 4 :=
        div_le_div₀ (by positivity) hnum_abs (by positivity) hden_ge
    _ = 4 := by
        field_simp

/-- Tail bound: `|boseReg0 x| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`. -/
lemma boseReg0_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |boseReg0 x| ≤ 4 * Real.exp (-x) + 1 / x ^ 2 := by
  set_option backward.isDefEq.respectTransparency false in
    have hxpos : (0 : ℝ) < x := by linarith
    have hbose_pos : 0 < boseKernel x := by
      rw [boseKernel]
      have h1 : Real.exp (-x) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      have h2 : 0 < 1 - Real.exp (-x) := by linarith
      positivity
    have hbose_le : boseKernel x ≤ 4 * Real.exp (-x) := by
      rw [boseKernel]
      have hexp1 : Real.exp (-x) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        linarith
      have he1 : Real.exp (-1) ≤ 1 / 2 := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
        have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_pos (-1),
          mul_le_mul_of_nonneg_left h2e (Real.exp_pos (-1)).le]
      have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-x) := by linarith
      have hden_sq : (1 : ℝ) / 4 ≤ (1 - Real.exp (-x)) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by nlinarith : (0:ℝ) < (1 - Real.exp (-x)) ^ 2)]
      nlinarith [Real.exp_pos (-x)]
    have hsplit : |boseReg0 x| ≤ boseKernel x + 1 / x ^ 2 := by
      rw [boseReg0]
      calc |boseKernel x - 1 / x ^ 2|
          ≤ |boseKernel x| + |1 / x ^ 2| := abs_sub _ _
        _ = boseKernel x + 1 / x ^ 2 := by
            rw [abs_of_pos hbose_pos, abs_of_pos (by positivity : (0:ℝ) < 1 / x ^ 2)]
    linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the Bose antiderivative (R10 bricks 8–12)

`F(x) = 1/x − 1/(eˣ−1)` has `F′ = boseReg0` on `(0,∞)`, `F → 0` at `∞`, `F → 1/2` at `0⁺`
(squeeze via the order-3 bound), with the finite FTC `∫_a^b boseReg0 = F(b) − F(a)`.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The antiderivative `1/x − 1/(eˣ−1)`. -/
noncomputable def boseAntideriv (x : ℝ) : ℝ :=
  1 / x - 1 / (Real.exp x - 1)

/-- `F′ = boseReg0` on `(0,∞)`. -/
lemma boseAntideriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseAntideriv (boseReg0 x) x := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / x ^ 2)) x := by
    have := hasDerivAt_inv hx.ne'
    simpa [one_div] using this
  have hexp : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => 1 / (Real.exp x - 1))
      (-(Real.exp x / (Real.exp x - 1) ^ 2)) x := by
    have := hexp.inv hypos.ne'
    simpa [one_div, div_eq_mul_inv] using this
  have hsub := h1.sub h2
  have heq : -(1 / x ^ 2) - -(Real.exp x / (Real.exp x - 1) ^ 2) = boseReg0 x := by
    rw [boseReg0, boseKernel_eq_exp_form hx]
    ring
  rw [← heq]
  exact hsub

/-- `boseReg0` is continuous at every `x > 0`. -/
lemma boseReg0_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt boseReg0 x := by
  have hlt : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : (1 - Real.exp (-x)) ^ 2 ≠ 0 := by
    have : 0 < 1 - Real.exp (-x) := by linarith
    positivity
  have hK : ContinuousAt boseKernel x := by
    apply ContinuousAt.div
    · exact (Real.continuous_exp.comp continuous_neg).continuousAt
    · exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).pow 2).continuousAt
    · exact hden
  have hI : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x := by
    apply ContinuousAt.div continuousAt_const ((continuous_pow 2).continuousAt)
    exact pow_ne_zero 2 hx.ne'
  exact hK.sub hI

/-- Finite FTC for `boseReg0`. -/
lemma intervalIntegral_boseReg0_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, boseReg0 x = boseAntideriv b - boseAntideriv a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact boseAntideriv_hasDerivAt (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (boseReg0_continuousAt (lt_of_lt_of_le ha hx.1)).continuousWithinAt

/-- `F → 0` at `∞`. -/
lemma boseAntideriv_tendsto_atTop : Tendsto boseAntideriv atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have h2 : Tendsto (fun x : ℝ => 1 / (Real.exp x - 1)) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun x : ℝ => Real.exp x - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) Real.tendsto_exp_atTop
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hcomp
    simpa [one_div, Function.comp] using this
  have hfin := h1.sub h2
  rw [sub_zero] at hfin
  refine hfin.congr fun x => ?_
  rw [boseAntideriv]

/-- `F → 1/2` at `0⁺`. -/
lemma boseAntideriv_tendsto_zero_right :
    Tendsto boseAntideriv (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
      fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- numerator limit: (eˣ−1−x)/x² → 1/2
  have hnum : Tendsto (fun x : ℝ => (Real.exp x - 1 - x) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        ‖(Real.exp x - 1 - x) / x ^ 2 - 1 / 2‖ ≤ x := by
      filter_upwards [hmem] with x hx
      have hδ := exp_sub_one_sub_self_sq_bound hx.1.le hx.2
      rw [Real.norm_eq_abs]
      have hxne : x ≠ 0 := hx.1.ne'
      have heq : (Real.exp x - 1 - x) / x ^ 2 - 1 / 2
          = (Real.exp x - 1 - x - x ^ 2 / 2) / x ^ 2 := by
        field_simp
      rw [heq, abs_div, abs_of_pos (pow_pos hx.1 2),
        div_le_iff₀ (pow_pos hx.1 2)]
      calc |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3 := hδ
        _ = x * x ^ 2 := by ring
    have hz := squeeze_zero_norm' hbound hx0
    have hfin := hz.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    rw [zero_add] at hfin
    refine hfin.congr fun x => ?_
    ring
  -- denominator limit: (eˣ−1)/x → 1
  have hden : Tendsto (fun x : ℝ => (Real.exp x - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        ‖(Real.exp x - 1) / x - 1‖ ≤ 2 * x := by
      filter_upwards [hmem] with x hx
      have hδ := exp_sub_one_sub_self_sq_bound hx.1.le hx.2
      have hδhi := (abs_le.mp hδ).2
      have hδlo := (abs_le.mp hδ).1
      rw [Real.norm_eq_abs]
      have hxne : x ≠ 0 := hx.1.ne'
      have heq : (Real.exp x - 1) / x - 1 = (Real.exp x - 1 - x) / x := by
        field_simp
      rw [heq, abs_div, abs_of_pos hx.1, div_le_iff₀ hx.1]
      rw [abs_le]
      constructor
      · nlinarith [hx.1.le, hx.2]
      · nlinarith [hx.1.le, hx.2]
    have h2x : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := hx0.const_mul (2 : ℝ)
      rwa [mul_zero] at hc
    have hz := squeeze_zero_norm' hbound h2x
    have hfin := hz.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [zero_add] at hfin
    refine hfin.congr fun x => ?_
    ring
  -- quotient
  have hquot := hnum.div hden (by norm_num)
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : (0 : ℝ) < x := hx
  have hy : 0 < Real.exp x - 1 := by
    have := Real.add_one_lt_exp (x := x) hxpos.ne'
    linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hyne : Real.exp x - 1 ≠ 0 := hy.ne'
  rw [Pi.div_apply, boseAntideriv]
  field_simp

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the boseReg0 integral (R10 bricks 7, 13)

`boseReg0` is integrable on `(0,∞)` (bounded by 4 on `(0,1]`, dominated by
`4e^{−x} + 1/x²` beyond 1) and

  `∫_{(0,∞)} boseReg0 = −1/2`,

via the antiderivative, the `ε → 0⁺` cut (`|∫_{(0,ε]}| ≤ 4ε`), and `F(0⁺) = 1/2`,
`F(∞) = 0`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `boseReg0` is globally measurable (as a total formula). -/
lemma boseReg0_measurable : Measurable boseReg0 := by
  unfold boseReg0 boseKernel
  measurability

/-- Integrability on `(0,1]`. -/
lemma boseReg0_integrableOn_Ioc01 : IntegrableOn boseReg0 (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 4)
  · rw [Real.volume_Ioc]
    norm_num
  · exact boseReg0_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact boseReg0_bdd_near_zero hx.1 hx.2

/-- Integrability on `(1,∞)`. -/
lemma boseReg0_integrableOn_Ioi1 : IntegrableOn boseReg0 (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have haesm : AEStronglyMeasurable boseReg0 (volume.restrict (Set.Ioi (1:ℝ))) :=
    boseReg0_measurable.aestronglyMeasurable
  -- dominating function
  have hg1 : IntegrableOn (fun x : ℝ => 4 * Real.exp (-x)) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-1 * x)) (Set.Ioi 1) :=
      exp_neg_integrableOn_Ioi 1 one_pos
    have hbase2 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 1) := by
      refine hbase.congr_fun (fun x _hx => ?_) hmeas
      norm_num
    have hfinal := hbase2.const_mul (4 : ℝ)
    exact hfinal
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg := hg1.add hg2
  apply Integrable.mono' hg haesm
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact boseReg0_tail_bound hx.le

/-- **Integrability of `boseReg0` on `(0,∞)`** (R10 brick 7). -/
lemma boseReg0_integrable_Ioi : IntegrableOn boseReg0 (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact boseReg0_integrableOn_Ioc01.union boseReg0_integrableOn_Ioi1

/-- The tail integral: `∫_{(1,∞)} boseReg0 = −F(1)`. -/
lemma integral_Ioi_one_boseReg0 :
    ∫ x in Set.Ioi 1, boseReg0 x = -boseAntideriv 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := boseAntideriv) (f' := boseReg0) (a := 1)
    (fun x hx => boseAntideriv_hasDerivAt (lt_of_lt_of_le zero_lt_one hx))
    boseReg0_integrableOn_Ioi1
    boseAntideriv_tendsto_atTop
  rw [h]
  ring

/-- The near-zero piece: `∫_{(0,1]} boseReg0 = F(1) − 1/2`. -/
lemma integral_Ioc_zero_one_boseReg0 :
    ∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x = boseAntideriv 1 - 1 / 2 := by
  -- for every ε ∈ (0,1]: ∫_{(0,1]} = ∫_{(0,ε]} + (F 1 − F ε)
  have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x
        = (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε) := by
    intro ε hε hε1
    have hsplit : Set.Ioc (0:ℝ) ε ∪ Set.Ioc ε 1 = Set.Ioc 0 1 :=
      Set.Ioc_union_Ioc_eq_Ioc hε.le hε1
    have hdisj : Disjoint (Set.Ioc (0:ℝ) ε) (Set.Ioc ε 1) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hint1 : IntegrableOn boseReg0 (Set.Ioc (0:ℝ) ε) :=
      boseReg0_integrableOn_Ioc01.mono_set
        (Set.Ioc_subset_Ioc le_rfl hε1)
    have hint2 : IntegrableOn boseReg0 (Set.Ioc ε 1) :=
      boseReg0_integrableOn_Ioc01.mono_set
        (Set.Ioc_subset_Ioc hε.le le_rfl)
    have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2
    rw [hsplit] at hunion
    rw [hunion]
    congr 1
    -- ∫_{(ε,1]} = F 1 − F ε via the interval FTC
    have hftc := intervalIntegral_boseReg0_eq hε hε1
    rw [← hftc, intervalIntegral.integral_of_le hε1]
  -- the near-zero piece is O(ε)
  have hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x| ≤ 4 * ε := by
    intro ε hε hε1
    have hbound : ∀ x ∈ Set.Ioc (0:ℝ) ε, ‖boseReg0 x‖ ≤ 4 := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact boseReg0_bdd_near_zero hx.1 (le_trans hx.2 hε1)
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioc (0:ℝ) ε) (C := 4)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hbound
    rw [Real.norm_eq_abs] at h
    calc |∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x|
        ≤ 4 * (volume (Set.Ioc (0:ℝ) ε)).toReal := h
      _ = 4 * ε := by
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
          ring
  -- pass to the limit ε → 0⁺
  have htend : Tendsto
      (fun ε : ℝ => (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε))
      (𝓝[>] (0:ℝ)) (𝓝 (0 + (boseAntideriv 1 - 1 / 2))) := by
    apply Tendsto.add
    · -- the small piece → 0 by squeeze
      have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
          ‖∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x‖ ≤ 4 * ε := by
        have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
            fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
        filter_upwards [hmem] with ε hε
        rw [Real.norm_eq_abs]
        exact hsmall ε hε.1 hε.2
      have hgten : Tendsto (fun ε : ℝ => 4 * ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hx0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have h4 := hx0.const_mul (4:ℝ)
        rwa [mul_zero] at h4
      exact squeeze_zero_norm' hb hgten
    · apply Tendsto.sub tendsto_const_nhds
      exact boseAntideriv_tendsto_zero_right
  rw [zero_add] at htend
  -- the function is eventually constant = ∫_{(0,1]}
  have hconst : Tendsto
      (fun ε : ℝ => (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x)) := by
    have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
        fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hmem] with ε hε
    exact (hkey ε hε.1 hε.2)
  exact tendsto_nhds_unique hconst htend

/-- **`∫_{(0,∞)} boseReg0 = −1/2`** (R10 brick 13). -/
theorem integral_boseReg0_Ioi :
    ∫ x in Set.Ioi (0:ℝ), boseReg0 x = -(1 / 2 : ℝ) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi 1) :=
    Set.Ioc_disjoint_Ioi le_rfl
  have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    boseReg0_integrableOn_Ioc01 boseReg0_integrableOn_Ioi1
  rw [hsplit] at hunion
  rw [hunion, integral_Ioc_zero_one_boseReg0, integral_Ioi_one_boseReg0]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the boseReg0 derivative (R10 bricks 14, 15, 17)

`boseReg0′(x) = −eˣ(eˣ+1)/(eˣ−1)³ + 2/x³` on `(0,∞)`, with the tail bound
`|boseReg0′| ≤ 16e^{−x/2} + 2/x³` for `x ≥ 1`.  (The near-zero derivative bound —
brick 16 — needs the degree-6 cancellation certificate and is a separate brick.)
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `boseReg0` has derivative `boseReg0Deriv` on `(0,∞)`. -/
lemma boseReg0_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseReg0 (boseReg0Deriv x) x := by
  have hy : 0 < Real.exp x - 1 := by
    have := Real.add_one_lt_exp (x := x) hx.ne'
    linarith
  -- exp-form kernel derivative
  have hker : HasDerivAt (fun y : ℝ => Real.exp y / (Real.exp y - 1) ^ 2)
      (-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun y : ℝ => (Real.exp y - 1) ^ 2)
        (2 * (Real.exp x - 1) ^ 1 * Real.exp x) x := by
      exact ((Real.hasDerivAt_exp x).sub_const 1).pow 2
    have hne : ((Real.exp x - 1) ^ 2) ≠ 0 := by positivity
    have hdiv := h1.div h2 hne
    convert hdiv using 1
    field_simp
    ring
  -- derivative of 1/y²
  have hinv : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 / x ^ 3)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ 1) x := hasDerivAt_pow 2 x
    have h2 := h1.inv (pow_ne_zero 2 hx.ne')
    have heq : -(2 * x ^ 1) / (x ^ 2) ^ 2 = -(2 / x ^ 3) := by
      field_simp
    have h3 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 / x ^ 3)) x := by
      rw [← heq]
      convert h2 using 1
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [one_div]
  have hsub := hker.sub hinv
  -- transfer along boseReg0 = exp-form − 1/x² near x
  have hev : boseReg0 =ᶠ[𝓝 x]
      fun y => Real.exp y / (Real.exp y - 1) ^ 2 - 1 / y ^ 2 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
    rw [boseReg0, boseKernel_eq_exp_form hy]
  have hfinal : HasDerivAt boseReg0
      (-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 - -(2 / x ^ 3)) x :=
    hsub.congr_of_eventuallyEq hev
  have : -(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 - -(2 / x ^ 3)
      = boseReg0Deriv x := by
    rw [boseReg0Deriv]
    ring
  rwa [this] at hfinal

/-- Tail derivative bound: `|boseReg0′(x)| ≤ 16e^{−x/2} + 2/x³` for `x ≥ 1`. -/
lemma boseReg0Deriv_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |boseReg0Deriv x| ≤ 16 * Real.exp (-x / 2) + 2 / x ^ 3 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp x := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    calc (2 : ℝ) ≤ Real.exp 1 := h1
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hy : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  have hypos : 0 < Real.exp x - 1 := by linarith
  have hepos := Real.exp_pos x
  -- the exponential piece: e^x(e^x+1)/(e^x−1)³ ≤ 16e^{−x}
  have hmain : Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3
      ≤ 16 * Real.exp (-x) := by
    have hnum_le : Real.exp x * (Real.exp x + 1) ≤ 2 * Real.exp x ^ 2 := by
      nlinarith [hepos, he2]
    have hden_ge : (Real.exp x / 2) ^ 3 ≤ (Real.exp x - 1) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity) hy
    have hden3 : (Real.exp x / 2) ^ 3 = Real.exp x ^ 3 / 8 := by ring
    have hstep : Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3
        ≤ (2 * Real.exp x ^ 2) / (Real.exp x ^ 3 / 8) := by
      apply div_le_div₀ (by positivity) hnum_le (by positivity)
      rw [← hden3]
      exact hden_ge
    have hsimp : (2 * Real.exp x ^ 2) / (Real.exp x ^ 3 / 8) = 16 / Real.exp x := by
      field_simp
      ring
    rw [hsimp] at hstep
    rw [show (16 : ℝ) * Real.exp (-x) = 16 / Real.exp x by
      rw [Real.exp_neg]
      field_simp]
    exact hstep
  have hexp_half : Real.exp (-x) ≤ Real.exp (-x / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [boseReg0Deriv]
  calc |-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3|
      ≤ |(-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3)| + |2 / x ^ 3| :=
        abs_add_le _ _
    _ = Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3 := by
        rw [abs_of_pos (by positivity : (0:ℝ) < 2 / x ^ 3)]
        congr 1
        rw [abs_of_nonpos (by
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [hepos]
          · positivity)]
        ring
    _ ≤ 16 * Real.exp (-x) + 2 / x ^ 3 := by linarith [hmain]
    _ ≤ 16 * Real.exp (-x / 2) + 2 / x ^ 3 := by nlinarith [hexp_half]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: integrability of the derivative (R10 brick 18)

`boseReg0′` is integrable on `(0,∞)`: bounded by 32 on `(0,1]`, dominated by
`16e^{−x/2} + 2/x³` beyond 1.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `boseReg0Deriv` is globally measurable. -/
lemma boseReg0Deriv_measurable : Measurable boseReg0Deriv := by
  unfold boseReg0Deriv
  measurability

/-- Integrability of `boseReg0′` on `(0,1]`. -/
lemma boseReg0Deriv_integrableOn_Ioc01 : IntegrableOn boseReg0Deriv (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 32)
  · rw [Real.volume_Ioc]
    norm_num
  · exact boseReg0Deriv_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact boseReg0Deriv_bdd_near_zero hx.1 hx.2

/-- Integrability of `boseReg0′` on `(1,∞)`. -/
lemma boseReg0Deriv_integrableOn_Ioi1 : IntegrableOn boseReg0Deriv (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have hg1 : IntegrableOn (fun x : ℝ => 16 * Real.exp (-x / 2)) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(1/2) * x)) (Set.Ioi 1) :=
      exp_neg_integrableOn_Ioi 1 (by norm_num : (0:ℝ) < 1/2)
    have hbase2 : IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Set.Ioi 1) := by
      refine hbase.congr_fun (fun x _hx => ?_) hmeas
      ring_nf
    exact hbase2.const_mul (16 : ℝ)
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 3) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (2 : ℝ)
  have hg := hg1.add hg2'
  apply Integrable.mono' hg boseReg0Deriv_measurable.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  have hb := boseReg0Deriv_tail_bound hx.le
  have heq : (2 : ℝ) / x ^ 3 = 2 * (1 / x ^ 3) := by ring
  linarith [le_of_eq heq]

/-- **Integrability of `boseReg0′` on `(0,∞)`** (R10 brick 18). -/
lemma boseReg0Deriv_integrable_Ioi : IntegrableOn boseReg0Deriv (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact boseReg0Deriv_integrableOn_Ioc01.union boseReg0Deriv_integrableOn_Ioi1

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

/-- `Σ_d d² e^{−dz}` in closed form. -/
noncomputable def boseKernel2 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + Real.exp (-z)) / (1 - Real.exp (-z)) ^ 3

/-- `boseKernel` has derivative `−boseKernel2` on `(0,∞)`. -/
lemma boseKernel_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel (-boseKernel2 z) z := by
  have hy : 0 < Real.exp z - 1 := by
    have := Real.add_one_lt_exp (x := z) hz.ne'
    linarith
  have hez := Real.exp_pos z
  -- boseKernel = boseReg0 + 1/x² near z
  have h1 := boseReg0_hasDerivAt hz
  have h2 : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 / z ^ 3)) z := by
    have ha : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z ^ 1) z := hasDerivAt_pow 2 z
    have hb := ha.inv (pow_ne_zero 2 hz.ne')
    have heq : -(2 * z ^ 1) / (z ^ 2) ^ 2 = -(2 / z ^ 3) := by
      field_simp
    have h3 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 / z ^ 3)) z := by
      rw [← heq]
      convert hb using 1
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [one_div]
  have hsum := h1.add h2
  have hev : boseKernel =ᶠ[𝓝 z] fun y => boseReg0 y + 1 / y ^ 2 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with y _hy
    rw [boseReg0]
    ring
  have hfinal := hsum.congr_of_eventuallyEq hev
  -- identify the derivative value
  have hval : boseReg0Deriv z + -(2 / z ^ 3) = -boseKernel2 z := by
    rw [boseReg0Deriv, boseKernel2]
    have hexp_form : Real.exp z * (Real.exp z + 1) / (Real.exp z - 1) ^ 3
        = Real.exp (-z) * (1 + Real.exp (-z)) / (1 - Real.exp (-z)) ^ 3 := by
      rw [Real.exp_neg]
      field_simp
    rw [← hexp_form]
    ring
  rwa [hval] at hfinal

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

/-- `boseKernel2 ≥ 0` on `(0,∞)`. -/
lemma boseKernel2_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel2 z := by
  have h1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel2]
  positivity

/-- Tail comparison: `boseKernel2(z) ≤ 2e^{−z}/(1−e^{−a})³` for `z ≥ a > 0`. -/
lemma boseKernel2_le {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) :
    boseKernel2 z ≤ 2 * Real.exp (-z) / (1 - Real.exp (-a)) ^ 3 := by
  have hea : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hda : 0 < 1 - Real.exp (-a) := by linarith
  have hez : Real.exp (-z) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hdz : 0 < 1 - Real.exp (-z) := by linarith
  have hd_mono : 1 - Real.exp (-a) ≤ 1 - Real.exp (-z) := by linarith
  rw [boseKernel2]
  apply div_le_div₀ (by positivity)
  · have h2 : 1 + Real.exp (-z) ≤ 2 := by
      have := Real.exp_pos (-z)
      linarith [hez, hea]
    nlinarith [Real.exp_pos (-z)]
  · positivity
  · exact pow_le_pow_left₀ hda.le hd_mono 3

/--
**The `M₁` Lambert identity** (termwise differentiation of the `M₀` identity):

  `Σ_m m·σ(m)e^{−tm} = Σ_k k·boseKernel2(tk)`.
-/
theorem sigmaMoment_one_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 1 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (t * (k : ℝ)) := by
  classical
  have ht2 : 0 < t / 2 := by linarith
  set s := Set.Ioi (t / 2) with hsdef
  have hs_open : IsOpen s := isOpen_Ioi
  have hs_conn : IsPreconnected s := (convex_Ioi _).isPreconnected
  have hts : t ∈ s := by
    rw [hsdef]
    exact Set.mem_Ioi.mpr (by linarith)
  set r := Real.exp (-(t / 2)) with hrdef
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    linarith
  have hr0 : 0 < r := Real.exp_pos _
  -- ===== σ-side =====
  set fσ := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else -((m : ℝ) * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
  have hσ_deriv : ∀ m : ℕ, ∀ u ∈ s, HasDerivAt (fσ m) (fσ' m u) u := by
    intro m u _hu
    by_cases hm : m = 0
    · subst hm
      simp only [hfσdef, hfσ'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hfσdef, hfσ'def, if_neg hm]
      have hinner : HasDerivAt (fun u : ℝ => -u * (m : ℝ)) (-(m : ℝ)) u := by
        simpa using ((hasDerivAt_id u).neg.mul_const ((m : ℝ)))
      have hexp := (Real.hasDerivAt_exp (-u * (m : ℝ))).comp u hinner
      have := hexp.const_mul (Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s, ‖fσ' m u‖ ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m := by
    intro m u hu
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
        have := sigmaR_nonneg m
        positivity)]
      have hum : Real.exp (-u * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hu2 : t / 2 < u := hu
        have hm0 : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hm
        nlinarith
      have := sigmaR_nonneg m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      exact mul_le_mul_of_nonneg_left hum (by positivity)
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 1 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rw [habs] at this
    refine this.congr fun m => ?_
    rw [pow_one]
  have hσ_at_t : Summable (fun m : ℕ => fσ m t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) hσ_u_summable
    by_cases hm : m = 0
    · subst hm
      simp [hfσdef]
    · simp only [hfσdef, if_neg hm]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := sigmaR_nonneg m
        positivity)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hum : Real.exp (-t * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hσn := sigmaR_nonneg m
      have hs1 : Sigma.sigmaR m * Real.exp (-t * (m : ℝ)) ≤ Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum hσn
      have hs2 : Sigma.sigmaR m * r ^ m ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m := by
        nlinarith [mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hσn) (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else boseKernel (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel2 (u * (k : ℝ))) * (k : ℝ)) with hgB'def
  set CB := (2:ℝ) / (1 - Real.exp (-(t / 2))) ^ 3 with hCBdef
  have hCB0 : 0 < CB := by
    rw [hCBdef]
    have : Real.exp (-(t / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have : 0 < 1 - Real.exp (-(t / 2)) := by linarith
    positivity
  have hB_deriv : ∀ k : ℕ, ∀ u ∈ s, HasDerivAt (gB k) (gB' k u) u := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp only [hgBdef, hgB'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hgBdef, hgB'def, if_neg hk]
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hu0 : 0 < u := lt_trans ht2 hu
      have hukpos : 0 < u * (k : ℝ) := by positivity
      have hinner : HasDerivAt (fun u : ℝ => u * (k : ℝ)) ((k : ℝ)) u := by
        simpa using (hasDerivAt_id u).mul_const ((k : ℝ))
      have houter := boseKernel_hasDerivAt hukpos
      have := houter.comp u hinner
      convert this using 1
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) * CB * r ^ k := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hu2 : t / 2 < u := hu
      have hu0 : 0 < u := lt_trans ht2 hu2
      have hukpos : 0 < u * (k : ℝ) := mul_pos hu0 (by linarith)
      have hbk2_nonneg := boseKernel2_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk2_nonneg,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel2_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel2 (u * (k : ℝ)) * (k : ℝ)
          ≤ (2 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (2 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) * (k : ℝ)
          = (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k
          = (k : ℝ) * CB * r ^ k := by
        rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) * r ^ k) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)).summable
    have := hbase.mul_left CB
    refine this.congr fun k => ?_
    ring
  have hB_at_t : Summable (fun k : ℕ => gB k t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hB_u_summable.congr (fun k => rfl))
    by_cases hk : k = 0
    · subst hk
      simp [hgBdef]
    · simp only [hgBdef, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hbk_pos : 0 < boseKernel (t * (k : ℝ)) := by
        rw [boseKernel]
        have h1 : Real.exp (-(t * (k : ℝ))) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        have h2 : 0 < 1 - Real.exp (-(t * (k : ℝ))) := by linarith
        positivity
      rw [Real.norm_eq_abs, abs_of_pos hbk_pos]
      -- boseKernel(tk) ≤ boseKernel2(tk) ≤ CB·r^k ≤ k·CB·r^k
      have h2 : boseKernel (t * (k : ℝ)) ≤ CB * r ^ k := by
        have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
        have hea : Real.exp (-(t / 2)) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        have hda : 0 < 1 - Real.exp (-(t / 2)) := by linarith
        have hez : Real.exp (-(t * (k : ℝ))) ≤ Real.exp (-(t / 2)) := by
          apply Real.exp_le_exp.mpr
          linarith
        have hdz : 0 < 1 - Real.exp (-(t * (k : ℝ))) := by linarith
        have hd_mono : 1 - Real.exp (-(t / 2)) ≤ 1 - Real.exp (-(t * (k : ℝ))) := by
          linarith
        have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
          rw [hrdef, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          nlinarith
        rw [boseKernel, hCBdef]
        have ho1 : Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t * (k : ℝ)))) ^ 2
            ≤ Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 2 := by
          apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          exact pow_le_pow_left₀ hda.le hd_mono 2
        have ho2 : Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 2
            ≤ (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k := by
          rw [div_eq_mul_inv, mul_comm]
          have hkey : ((1 - Real.exp (-(t / 2))) ^ 2)⁻¹
              ≤ 2 / (1 - Real.exp (-(t / 2))) ^ 3 := by
            rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hda, Real.exp_pos (-(t / 2))]
          apply mul_le_mul hkey hexp_le (Real.exp_pos _).le (by positivity)
        exact le_trans ho1 ho2
      have hf2 : CB * r ^ k ≤ (k : ℝ) * CB * r ^ k := by
        nlinarith [pow_pos hr0 k, hCB0]
      exact le_trans h2 hf2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_zero_lambert (t := u) hu0
    have hLHS : sigmaMoment 0 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
      refine tsum_congr fun m => ?_
      by_cases hm : m = 0
      · subst hm
        simp [hfσdef]
      · simp only [hfσdef, if_neg hm]
        rw [pow_zero, one_mul]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else boseKernel (u * (k : ℝ)))
        = ∑' k : ℕ, gB k u := by
      refine tsum_congr fun k => ?_
      by_cases hk : k = 0
      · subst hk
        simp [hgBdef]
      · simp only [hgBdef, if_neg hk]
    rw [← hLHS, hML, ← hRHS]
  -- transfer the derivative + uniqueness
  have hA' : HasDerivAt (fun z => ∑' k : ℕ, gB k z) (∑' m : ℕ, fσ' m t) t :=
    hA.congr_of_eventuallyEq hEq.symm
  have huniq := hA'.unique hB
  -- huniq : Σ' fσ' m t = Σ' gB' k t; negate
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 1 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      ring
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (t * (k : ℝ))) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · subst hk
      simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      ring
  rw [hLHS', hRHS'] at huniq
  linarith [huniq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: crude power bounds for the Lambert moments

`Σ' m^j x^m ≤ j!/(1−x)^{j+1}` (via `m^j ≤ j!·C(m+j,j)` and the choose-geometric sum), hence
`M_r(t) ≤ (r+2)!·2^{r+3}/t^{r+3}` on `0 < t ≤ 1` — the tail-control input for the `r = 2,3,4`
moments in the §5–7 kernel-mass assembly.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ' m^j x^m ≤ j!/(1−x)^{j+1}` for `0 ≤ x < 1`. -/
lemma tsum_pow_mul_geometric_le (j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' m : ℕ, (m : ℝ) ^ j * x ^ m ≤ (j.factorial : ℝ) / (1 - x) ^ (j + 1) := by
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hsum1 : Summable (fun m : ℕ => (m : ℝ) ^ j * x ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j hxn
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one j hxn
  have hsum2 : Summable
      (fun m : ℕ => (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m) := by
    have hbase := hchoose.summable.mul_left (j.factorial : ℝ)
    refine hbase.congr fun m => ?_
    ring
  have hle : ∀ m : ℕ, (m : ℝ) ^ j * x ^ m
      ≤ (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m := by
    intro m
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0 m)
    have hnat : m ^ j ≤ j.factorial * (m + j).choose j := by
      have h1 : (m + 1) ^ j ≤ (m + j).descFactorial j := by
        have h := Nat.pow_sub_le_descFactorial (m + j) j
        have harg : m + j + 1 - j = m + 1 := by omega
        rwa [harg] at h
      have h2 : m ^ j ≤ (m + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ m) j
      have h3 : (m + j).descFactorial j = j.factorial * (m + j).choose j := by
        have hd := Nat.factorial_dvd_descFactorial (m + j) j
        rw [Nat.choose_eq_descFactorial_div_factorial, Nat.mul_div_cancel' hd]
      exact le_trans h2 (le_trans h1 (le_of_eq h3))
    exact_mod_cast hnat
  have hmain := hsum1.tsum_le_tsum hle hsum2
  refine le_trans hmain (le_of_eq ?_)
  have hfac : ∀ m : ℕ, (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m
      = (j.factorial : ℝ) * ((((m + j).choose j : ℕ) : ℝ) * x ^ m) := by
    intro m
    ring
  rw [tsum_congr hfac, tsum_mul_left, hchoose.tsum_eq]
  rw [mul_one_div]

/-- `1 − e^{−t} ≥ t/2` on `0 < t ≤ 1`. -/
lemma one_sub_exp_neg_ge_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hpos : (0:ℝ) < 1 + t := by linarith
  have h3 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le hpos
    linarith
  have h4 : 1 / (1 + t) ≤ 1 - t / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: shifted Basel tail `Σ' 1/(i+N+1)² ≤ 2/(N+1)`

The polynomial-tail input for the weighted-decay keystone, via `sum_Ioo_inv_sq_le`.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Finset
open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Basel tail (shifted form): `Σ'_{i} 1/(i+N+1)² ≤ 2/(N+1)`. -/
lemma tail_inv_sq_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the weighted-decay summation bound (keystone for M₁, M₂)

For `f` bounded by `Cf` on `(0,1]` and by `Bf·e^{−z/2} + Df/z^{j+2}` on `(1,∞)`,

  `Σ'_{k≥1} k^j·|f(tk)| ≤ K/t^{j+1}`  on `0 < t ≤ 1`,

with `K = Cf·2^{j+1} + Bf·j!·4^{j+1} + 2 Df`.  Three buckets: near-origin (`k ≤ 1/t`, the
`Cf` bound), exponential tail (`tsum_pow_mul_geometric_le`), polynomial tail (`tail_inv_sq_shift`).
Instantiated for `M₁` (`j=1`, `f=boseReg0′`) and `M₂` (`j=2`, `f=boseReg0″`).  Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Weighted-decay summation bound** (keystone). -/
lemma weighted_decay_sum_bound (j : ℕ) (f : ℝ → ℝ) (Cf Bf Df : ℝ)
    (hCf : 0 ≤ Cf) (hBf : 0 ≤ Bf) (hDf : 0 ≤ Df)
    (h01 : ∀ z : ℝ, 0 < z → z ≤ 1 → |f z| ≤ Cf)
    (htail : ∀ z : ℝ, 1 < z → |f z| ≤ Bf * Real.exp (-z / 2) + Df / z ^ (j + 2))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∑' k : ℕ, if k = 0 then (0:ℝ) else (k : ℝ) ^ j * |f (t * (k : ℝ))|)
      ≤ (Cf * 2 ^ (j + 1) + Bf * (Nat.factorial j) * 4 ^ (j + 1) + 2 * Df)
          / t ^ (j + 1) := by
  classical
  set a : ℕ → ℝ := fun k => if k = 0 then (0:ℝ) else (k : ℝ) ^ j * |f (t * (k : ℝ))| with hadef
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    simp only [hadef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; positivity
  -- N = ⌊1/t⌋
  have htinv_pos : 0 < 1 / t := by positivity
  set N : ℕ := ⌊1 / t⌋₊ with hNdef
  have htinv_ge1 : (1:ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact Nat.le_floor (by exact_mod_cast htinv_ge1)
  have hNle : (N : ℝ) ≤ 1 / t := Nat.floor_le htinv_pos.le
  have hNlt : 1 / t < (N : ℝ) + 1 := by
    rw [hNdef]; exact Nat.lt_floor_add_one (1 / t)
  have htN_le1 : t * (N : ℝ) ≤ 1 := by
    rw [mul_comm, ← le_div_iff₀ ht0]; exact hNle
  have htNp1_gt1 : 1 < t * ((N : ℝ) + 1) := by
    rw [mul_comm, ← div_lt_iff₀ ht0]; exact hNlt
  -- exp dominator summability
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hexp_summ : Summable (fun k : ℕ => (k : ℝ) ^ j * Real.exp (-t / 2) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have hbasel_summ : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  -- tail summand bound (k = i+N+1 ≥ N+1, so t·k > 1)
  have htail_term : ∀ i : ℕ,
      a (i + N + 1) ≤ ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf
        + Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hk0 : (i + N + 1 : ℕ) ≠ 0 := by positivity
    simp only [hadef, if_neg hk0]
    set k : ℕ := i + N + 1 with hkdef
    have hkge : (N : ℝ) + 1 ≤ (k : ℝ) := by rw [hkdef]; push_cast; linarith
    have htk1 : 1 < t * (k : ℝ) :=
      lt_of_lt_of_le htNp1_gt1 (mul_le_mul_of_nonneg_left hkge ht0.le)
    have hb := htail (t * (k : ℝ)) htk1
    have hkpos : (0:ℝ) < (k : ℝ) := by positivity
    have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    have htne : t ≠ 0 := ht0.ne'
    have hpoly_eq : (k : ℝ) ^ j * (Df / (t * (k : ℝ)) ^ (j + 2))
        = Df / t ^ (j + 2) * (1 / (k : ℝ) ^ 2) := by
      rw [mul_pow, show (k : ℝ) ^ (j + 2) = (k : ℝ) ^ j * (k : ℝ) ^ 2 from by rw [pow_add]]
      field_simp
    calc (k : ℝ) ^ j * |f (t * (k : ℝ))|
        ≤ (k : ℝ) ^ j * (Bf * Real.exp (-(t * (k : ℝ)) / 2) + Df / (t * (k : ℝ)) ^ (j + 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf
            + Df / t ^ (j + 2) * (1 / (k : ℝ) ^ 2) := by
          rw [mul_add, hexp_eq, hpoly_eq]; ring
  -- summable shifted dominators
  have hshift_exp : Summable (fun i : ℕ =>
      ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf) := by
    have hsh := (summable_nat_add_iff (N + 1)).mpr hexp_summ
    have := hsh.mul_right Bf
    refine this.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by ring
    rw [he]
  have hshift_poly : Summable (fun i : ℕ =>
      Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have hsh : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have := (summable_nat_add_iff (N + 1)).mpr hbasel_summ
      refine this.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]
    exact hsh.mul_left _
  -- summability of a
  have ha_summ : Summable a := by
    rw [← summable_nat_add_iff (N + 1)]
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hshift_exp.add hshift_poly)
    · have := ha_nonneg (i + N + 1)
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]; exact this
    · have := htail_term i
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]; exact this
  -- decomposition
  have hsplit := (Summable.sum_add_tsum_nat_add (N + 1) ha_summ).symm
  rw [hsplit]
  -- FINITE BUCKET
  have hfin : (∑ k ∈ Finset.range (N + 1), a k) ≤ Cf * 2 ^ (j + 1) / t ^ (j + 1) := by
    have hterm : ∀ k ∈ Finset.range (N + 1), a k ≤ Cf * (N : ℝ) ^ j := by
      intro k hk
      simp only [hadef]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]; positivity
      · rw [if_neg hk0]
        have hkpos : (0:ℝ) < (k : ℝ) := by
          have : 0 < k := Nat.pos_of_ne_zero hk0; exact_mod_cast this
        have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
        have htkpos : 0 < t * (k : ℝ) := by positivity
        have htk1 : t * (k : ℝ) ≤ 1 := by
          calc t * (k : ℝ) ≤ t * (N : ℝ) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) ht0.le
            _ ≤ 1 := htN_le1
        have hfb := h01 (t * (k : ℝ)) htkpos htk1
        have hkjN : (k : ℝ) ^ j ≤ (N : ℝ) ^ j :=
          pow_le_pow_left₀ hkpos.le (by exact_mod_cast hkN) j
        calc (k : ℝ) ^ j * |f (t * (k : ℝ))| ≤ (N : ℝ) ^ j * Cf :=
              mul_le_mul hkjN hfb (abs_nonneg _) (by positivity)
          _ = Cf * (N : ℝ) ^ j := by ring
    have hsum_le := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
    rw [Nat.cast_add, Nat.cast_one] at hsum_le
    refine le_trans hsum_le ?_
    have hNp1 : ((N : ℝ) + 1) ≤ 2 / t := by
      have h1 : (N : ℝ) + 1 ≤ 1 / t + 1 := by linarith [hNle]
      have h2 : 1 / t + 1 ≤ 2 / t := by
        rw [div_add' _ _ _ ht0.ne', div_le_div_iff₀ ht0 ht0]; nlinarith [htinv_ge1]
      linarith
    have hNjt : (N : ℝ) ^ j ≤ 1 / t ^ j := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (N:ℝ)) hNle j
      rwa [div_pow, one_pow] at h
    have hprod : ((N : ℝ) + 1) * (N : ℝ) ^ j ≤ (2 / t) * (1 / t ^ j) :=
      mul_le_mul hNp1 hNjt (by positivity) (by positivity)
    have hrw : (2 / t) * (1 / t ^ j) = 2 / t ^ (j + 1) := by rw [pow_succ]; field_simp
    calc ((N : ℝ) + 1) * (Cf * (N : ℝ) ^ j)
        = Cf * (((N : ℝ) + 1) * (N : ℝ) ^ j) := by ring
      _ ≤ Cf * (2 / t ^ (j + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hCf; rw [← hrw]; exact hprod
      _ = Cf * 2 / t ^ (j + 1) := by ring
      _ ≤ Cf * 2 ^ (j + 1) / t ^ (j + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hCf
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- TAIL BUCKET
  have htail_le : (∑' i : ℕ, a (i + N + 1))
      ≤ (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
        + (∑' i : ℕ, Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have ha_tail_summ : Summable (fun i : ℕ => a (i + N + 1)) :=
      (summable_nat_add_iff (N + 1)).mpr ha_summ
    rw [← Summable.tsum_add hshift_exp hshift_poly]
    exact ha_tail_summ.tsum_le_tsum htail_term (hshift_exp.add hshift_poly)
  -- exp bucket
  have hexp_tail : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
      ≤ Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by
    have hwhole_summ : Summable (fun k : ℕ => (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf) :=
      hexp_summ.mul_right Bf
    have hle_whole : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
        ≤ (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf) := by
      have hshift_eq : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
          = ∑' i : ℕ, (((i + (N + 1) : ℕ)) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + (N + 1)) * Bf := by
        apply tsum_congr; intro i
        have he : i + N + 1 = i + (N + 1) := by ring
        rw [he]
      rw [hshift_eq, (Summable.sum_add_tsum_nat_add (N + 1) hwhole_summ).symm]
      have hfin_nonneg : 0 ≤ ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf := by
        apply Finset.sum_nonneg; intro k _; positivity
      linarith
    refine le_trans hle_whole ?_
    have htsum_eq : (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf)
        = Bf * ∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k := by
      rw [← tsum_mul_left]; apply tsum_congr; intro k; ring
    rw [htsum_eq]
    have hbase := tsum_pow_mul_geometric_le j hr0 hr1
    have hden : t / 4 ≤ 1 - Real.exp (-t / 2) := by
      have h1 : t / 2 / 2 ≤ 1 - Real.exp (-(t / 2)) :=
        one_sub_exp_neg_ge_half (by linarith) (by linarith)
      rw [show -(t / 2) = -t / 2 from by ring] at h1
      linarith
    have hpow : (t / 4) ^ (j + 1) ≤ (1 - Real.exp (-t / 2)) ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) hden _
    have hbase2 : (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k)
        ≤ (Nat.factorial j : ℝ) / (t / 4) ^ (j + 1) :=
      le_trans hbase (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
    have hrw : (Nat.factorial j : ℝ) / (t / 4) ^ (j + 1)
        = (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by rw [div_pow]; field_simp
    rw [hrw] at hbase2
    calc Bf * ∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k
        ≤ Bf * ((Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1)) :=
          mul_le_mul_of_nonneg_left hbase2 hBf
      _ = Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by ring
  -- poly bucket
  have hpoly_tail : (∑' i : ℕ, Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2))
      ≤ 2 * Df / t ^ (j + 1) := by
    rw [tsum_mul_left]
    have hbasel := tail_inv_sq_shift N
    have hstep : Df / t ^ (j + 2) * (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
        ≤ Df / t ^ (j + 2) * (2 / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hbasel (by positivity)
    refine le_trans hstep ?_
    have hN1t : 2 / ((N : ℝ) + 1) ≤ 2 * t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hNlt, ht0, mul_pos ht0 (show (0:ℝ) < (N:ℝ)+1 by positivity)]
    calc Df / t ^ (j + 2) * (2 / ((N : ℝ) + 1))
        ≤ Df / t ^ (j + 2) * (2 * t) :=
          mul_le_mul_of_nonneg_left hN1t (by positivity)
      _ = 2 * Df / t ^ (j + 1) := by rw [pow_succ]; field_simp
  -- assemble
  have htailbd : (∑' i : ℕ, a (i + N + 1))
      ≤ Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) + 2 * Df / t ^ (j + 1) :=
    le_trans htail_le (add_le_add hexp_tail hpoly_tail)
  have hfinal := add_le_add hfin htailbd
  refine le_trans hfinal (le_of_eq ?_)
  field_simp
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: `M₁` weak asymptotics

`|M₁(t) − 2(π²/6)/t³| ≤ 388/t²` on `0 < t ≤ 1`.  Split the Lambert identity
`M₁ = Σ'_{k} k·boseKernel2(tk)` via `boseKernel2 z = 2/z³ − boseReg0′(z)`: the singular part
sums (Basel) to `2(π²/6)/t³`, the remainder is `−Σ'_k k·boseReg0′(tk)`, bounded by the
weighted-decay keystone (`j=1`, `Cf=32`, `Bf=16`, `Df=2`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The kernel-derivative split: `boseKernel2 z = 2/z³ − boseReg0′(z)` for `z > 0`. -/
lemma boseKernel2_eq_inv_cube_sub_deriv {z : ℝ} (hz : 0 < z) :
    boseKernel2 z = 2 / z ^ 3 - boseReg0Deriv z := by
  have hy : 0 < Real.exp z - 1 := by
    have := Real.add_one_lt_exp (x := z) hz.ne'
    linarith
  rw [boseKernel2, boseReg0Deriv, Real.exp_neg]
  have hz3 : z ^ 3 ≠ 0 := by positivity
  have hexp : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  field_simp
  ring

/-- Global derivative bound: `|boseReg0′(z)| ≤ 64 e^{−z/2} + 2/z³` for all `z > 0`. -/
lemma boseReg0Deriv_global_bound {z : ℝ} (hz : 0 < z) :
    |boseReg0Deriv z| ≤ 64 * Real.exp (-z / 2) + 2 / z ^ 3 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := boseReg0Deriv_bdd_near_zero hz hz1
    have h2 : (32:ℝ) ≤ 64 * Real.exp (-z / 2) := by
      have hmono : Real.exp (-(1:ℝ) / 2) ≤ Real.exp (-z / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hhalf : (1:ℝ) / 2 ≤ Real.exp (-(1:ℝ) / 2) := by
        have := Real.add_one_le_exp (-(1:ℝ) / 2); linarith
      nlinarith [hmono, hhalf]
    have h3 : (0:ℝ) ≤ 2 / z ^ 3 := by positivity
    linarith
  · have h1 := boseReg0Deriv_tail_bound hz1.le
    have h2 : (16:ℝ) * Real.exp (-z / 2) ≤ 64 * Real.exp (-z / 2) := by
      have := Real.exp_pos (-z / 2); nlinarith
    linarith

/-- Summability of `k·|boseReg0′(tk)|`. -/
lemma summable_weighted_absDeriv {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => if k = 0 then (0:ℝ) else (k : ℝ) * |boseReg0Deriv (t * (k : ℝ))|) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hdom : Summable (fun k : ℕ =>
      (k : ℝ) * (64 * Real.exp (-t / 2) ^ k) + 2 / t ^ 3 * (1 / ((k : ℝ)) ^ 2)) := by
    apply Summable.add
    · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left 64
      refine this.congr fun k => ?_
      rw [pow_one]; ring
    · have hb : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      exact hb.mul_left _
  apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hdom
  · by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; positivity
  · by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hg := boseReg0Deriv_global_bound htkpos
      have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have htne : t ≠ 0 := ht.ne'
      have hpoly : (k : ℝ) * (2 / (t * (k : ℝ)) ^ 3) = 2 / t ^ 3 * (1 / (k : ℝ) ^ 2) := by
        rw [mul_pow, show (k : ℝ) ^ 3 = (k : ℝ) ^ 2 * (k : ℝ) from by ring]
        field_simp
      calc (k : ℝ) * |boseReg0Deriv (t * (k : ℝ))|
          ≤ (k : ℝ) * (64 * Real.exp (-(t * (k : ℝ)) / 2) + 2 / (t * (k : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_left hg hkpos.le
        _ = (k : ℝ) * (64 * Real.exp (-t / 2) ^ k) + 2 / t ^ 3 * (1 / (k : ℝ) ^ 2) := by
            rw [mul_add, hexp_eq, hpoly]

/-- **`M₁` weak asymptotics**: `|M₁(t) − 2(π²/6)/t³| ≤ 388/t²` on `0 < t ≤ 1`. -/
theorem sigmaMoment_one_asymp_weak {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 1 t - 2 * (Real.pi ^ 2 / 6) / t ^ 3| ≤ 388 / t ^ 2 := by
  classical
  have hML := sigmaMoment_one_lambert ht0
  -- the two guarded families
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) * boseReg0Deriv (t * (k : ℝ)) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (2 / t ^ 3) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  -- summability
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absDeriv ht0
    refine habs.congr fun k => ?_
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hmain_summ : Summable hmain := by
    have hb : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h0
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]; positivity
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]
    have := hb.mul_left (2 / t ^ 3)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  -- per-term: the lambert summand = hmain − hrem
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) * boseKernel2 (t * (k : ℝ)))
        = hmain k - hrem k := by
    intro k
    simp only [hmaindef, hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htkpos : 0 < t * (k : ℝ) := by positivity
      rw [boseKernel2_eq_inv_cube_sub_deriv htkpos]
      have htne : t ≠ 0 := ht0.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
  -- M₁ = Σ hmain − Σ hrem
  have hM1_eq : sigmaMoment 1 t = (∑' k, hmain k) - (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_sub hrem_summ]
  -- Σ hmain = 2Z/t³
  have hmain_eq : (∑' k, hmain k) = 2 * (Real.pi ^ 2 / 6) / t ^ 3 := by
    have : (∑' k, hmain k) = (2 / t ^ 3) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]
    ring
  -- bound |Σ hrem| via keystone
  have hrem_abs_bound : |∑' k, hrem k| ≤ 388 / t ^ 2 := by
    have hnorm : |∑' k, hrem k| ≤ ∑' k, |hrem k| := by
      have hns : Summable (fun k => ‖hrem k‖) := by
        have := summable_weighted_absDeriv ht0
        refine this.congr fun k => ?_
        simp only [hremdef]
        by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      have h1 := norm_tsum_le_tsum_norm hns
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
    refine le_trans hnorm ?_
    have habs_eq : (∑' k, |hrem k|)
        = ∑' k : ℕ, if k = 0 then (0:ℝ) else (k : ℝ) ^ 1 * |boseReg0Deriv (t * (k : ℝ))| := by
      apply tsum_congr; intro k
      simp only [hremdef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk, abs_mul, Nat.abs_cast, pow_one]
    rw [habs_eq]
    have hkey := weighted_decay_sum_bound 1 boseReg0Deriv 32 16 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun z hz0 hz1 => boseReg0Deriv_bdd_near_zero hz0 hz1)
      (fun z hz1 => boseReg0Deriv_tail_bound hz1.le)
      ht0 ht1
    refine le_trans hkey (le_of_eq ?_)
    norm_num
  -- conclude
  rw [hM1_eq, hmain_eq]
  have harr : (2 * (Real.pi ^ 2 / 6) / t ^ 3 - ∑' k, hrem k) - 2 * (Real.pi ^ 2 / 6) / t ^ 3
      = -(∑' k, hrem k) := by ring
  rw [harr, abs_neg]
  exact hrem_abs_bound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the Riemann-sum `O(1)` bound for `boseReg0`

`|Σ'_{k≥1} boseReg0(tk) − (−1/2)/t| ≤ ∫₀^∞ |boseReg0′|` — right-endpoint Riemann sums of
`boseReg0` with mesh `t` differ from `(1/t)·∫₀^∞ boseReg0 = −1/(2t)` by at most the total
variation, cell by cell via FTC.  This is the brick-22 engine (replaces the lost R12 draft).
Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Global pointwise bound: `|boseReg0 z| ≤ 4e^{−z} + 4/z²` on `(0,∞)`. -/
lemma boseReg0_abs_le_global {z : ℝ} (hz : 0 < z) :
    |boseReg0 z| ≤ 4 * Real.exp (-z) + 4 / z ^ 2 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := boseReg0_bdd_near_zero hz hz1
    have h2 : (4:ℝ) ≤ 4 / z ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : 0 < Real.exp (-z) := Real.exp_pos _
    linarith
  · have h1 := boseReg0_tail_bound hz1.le
    have h2 : |boseReg0 z| ≤ 4 * Real.exp (-z) + 1 / z ^ 2 := h1
    have h3 : (1:ℝ) / z ^ 2 ≤ 4 / z ^ 2 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-- Summability of the sample sums `Σ_k boseReg0(t(k+1))`. -/
lemma summable_boseReg0_samples {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => boseReg0 (t * ((k : ℝ) + 1))) := by
  have hr1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hr0 : (0:ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
  -- dominator: 4e^{−t(k+1)} + 4/(t(k+1))²
  have hgeo : Summable (fun k : ℕ => 4 * Real.exp (-t) ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left 4
    exact (summable_nat_add_iff 1).mpr h
  have hbasel : Summable (fun k : ℕ => 4 / (t * ((k : ℝ) + 1)) ^ 2) := by
    have hb0 : Summable (fun n : ℕ => (((n : ℝ) ^ (2:ℝ))⁻¹)) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hb1 := (summable_nat_add_iff 1).mpr hb0
    have hb : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
      refine hb1.congr fun k => ?_
      have hc : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
      rw [hc, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hb2 := hb.mul_left (4 / t ^ 2)
    refine hb2.congr fun k => ?_
    field_simp
  have hdom := hgeo.add hbasel
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hdom
  have hkpos : (0:ℝ) < t * ((k : ℝ) + 1) := by positivity
  have hglob := boseReg0_abs_le_global hkpos
  rw [Real.norm_eq_abs]
  have hexp : Real.exp (-(t * ((k : ℝ) + 1))) = Real.exp (-t) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc |boseReg0 (t * ((k : ℝ) + 1))|
      ≤ 4 * Real.exp (-(t * ((k : ℝ) + 1))) + 4 / (t * ((k : ℝ) + 1)) ^ 2 := hglob
    _ = 4 * Real.exp (-t) ^ (k + 1) + 4 / (t * ((k : ℝ) + 1)) ^ 2 := by rw [hexp]

/-- The mesh-`t` cell. -/
def cell (t : ℝ) (k : ℕ) : Set ℝ := Set.Ioc (t * (k : ℝ)) (t * ((k : ℝ) + 1))

lemma cell_measurable (t : ℝ) (k : ℕ) : MeasurableSet (cell t k) := measurableSet_Ioc

lemma cell_subset_Ioi {t : ℝ} (ht : 0 < t) (k : ℕ) : cell t k ⊆ Set.Ioi 0 := by
  intro x hx
  have h1 : t * (k : ℝ) < x := hx.1
  have h2 : (0:ℝ) ≤ t * (k : ℝ) := by positivity
  exact Set.mem_Ioi.mpr (lt_of_le_of_lt h2 h1)

lemma cell_pairwise_disjoint {t : ℝ} (ht : 0 < t) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => cell t k)) := by
  have key : ∀ {i j : ℕ}, i < j → Disjoint (cell t i) (cell t j) := by
    intro i j h
    rw [Set.disjoint_left]
    intro x hxi hxj
    have h1 : x ≤ t * ((i : ℝ) + 1) := hxi.2
    have h2 : t * (j : ℝ) < x := hxj.1
    have h3 : (i : ℝ) + 1 ≤ (j : ℝ) := by
      have hn : (i : ℕ) + 1 ≤ j := h
      exact_mod_cast hn
    nlinarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact (key h).symm

lemma iUnion_cell {t : ℝ} (ht : 0 < t) : (⋃ k : ℕ, cell t k) = Set.Ioi 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩
    exact cell_subset_Ioi ht k hk
  · intro hx
    have hxt : 0 < x / t := by positivity
    set n := ⌈x / t⌉₊ with hndef
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
    refine ⟨n - 1, ?_, ?_⟩
    · -- t·(n−1) < x
      have hlt : ((n : ℝ) - 1) < x / t := by
        have h := Nat.ceil_lt_add_one hxt.le
        have h2 : (n : ℝ) < x / t + 1 := by
          rw [hndef]
          exact_mod_cast h
        linarith
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have : (1:ℕ) ≤ n := hn1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      calc t * ((n : ℝ) - 1) < t * (x / t) := by
            apply mul_lt_mul_of_pos_left hlt ht
        _ = x := by field_simp
    · -- x ≤ t·((n−1)+1)
      have hle : x / t ≤ (n : ℝ) := Nat.le_ceil _
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        have : (1:ℕ) ≤ n := hn1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      calc x = t * (x / t) := by field_simp
        _ ≤ t * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_left hle ht.le

/-- Cell decomposition of `∫ boseReg0`. -/
lemma hasSum_cell_boseReg0 {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ∫ x in cell t k, boseReg0 x)
      (∫ x in Set.Ioi 0, boseReg0 x) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := boseReg0)
    (fun k => cell_measurable t k) (cell_pairwise_disjoint ht)
    (by rw [iUnion_cell ht]; exact boseReg0_integrable_Ioi)
  rwa [iUnion_cell ht] at h

/-- Cell decomposition of `∫ |boseReg0′|`. -/
lemma hasSum_cell_absDeriv {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ∫ x in cell t k, |boseReg0Deriv x|)
      (∫ x in Set.Ioi 0, |boseReg0Deriv x|) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := fun x => |boseReg0Deriv x|)
    (fun k => cell_measurable t k) (cell_pairwise_disjoint ht)
    (by rw [iUnion_cell ht]; exact boseReg0Deriv_integrable_Ioi.abs)
  rwa [iUnion_cell ht] at h

/-- **Cell FTC error**: right-endpoint sample vs cell integral. -/
lemma cell_error {t : ℝ} (ht : 0 < t) (k : ℕ) :
    |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|
      ≤ t * ∫ x in cell t k, |boseReg0Deriv x| := by
  set a := t * (k : ℝ) with hadef
  set b := t * ((k : ℝ) + 1) with hbdef
  have hab : a < b := by
    rw [hadef, hbdef]
    nlinarith
  have ha0 : 0 ≤ a := by positivity
  have hvol : b - a = t := by
    rw [hadef, hbdef]
    ring
  have hcell : cell t k = Set.Ioc a b := rfl
  -- integrability of boseReg0 and |boseReg0Deriv| on the cell
  have hint_f : IntegrableOn boseReg0 (Set.Ioc a b) :=
    boseReg0_integrable_Ioi.mono_set (by
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_le_of_lt ha0 hx.1))
  have hint_d : IntegrableOn (fun x => |boseReg0Deriv x|) (Set.Ioc a b) :=
    (boseReg0Deriv_integrable_Ioi.mono_set (by
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_le_of_lt ha0 hx.1))).abs
  -- pointwise: |f(b) − f(x)| ≤ ∫_cell |f'| for x in the cell
  have hptwise : ∀ x ∈ Set.Ioc a b,
      |boseReg0 b - boseReg0 x| ≤ ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt ha0 hx.1
    have hxb : x ≤ b := hx.2
    have hftc : ∫ y in x..b, boseReg0Deriv y = boseReg0 b - boseReg0 x := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro y hy
        rw [Set.uIcc_of_le hxb] at hy
        exact boseReg0_hasDerivAt (lt_of_lt_of_le hx0 hy.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxb]
        exact boseReg0Deriv_integrable_Ioi.mono_set (by
          intro y hy
          exact Set.mem_Ioi.mpr (lt_of_lt_of_le hx0 (le_of_lt hy.1)))
    rw [← hftc]
    have h1 : |∫ y in x..b, boseReg0Deriv y| ≤ ∫ y in x..b, |boseReg0Deriv y| := by
      exact intervalIntegral.abs_integral_le_integral_abs hxb
    have h2 : ∫ y in x..b, |boseReg0Deriv y| ≤ ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
      rw [intervalIntegral.integral_of_le hxb]
      apply setIntegral_mono_set hint_d
      · filter_upwards with y
        exact abs_nonneg _
      · apply HasSubset.Subset.eventuallyLE
        intro y hy
        exact ⟨lt_of_le_of_lt hx.1.le hy.1, hy.2⟩
    linarith
  -- t·f(b) = ∫_cell f(b)
  have hvolr : volume.real (Set.Ioc a b) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    exact hvol
  have hconst : ∫ _x in Set.Ioc a b, boseReg0 b = t * boseReg0 b := by
    rw [setIntegral_const, hvolr, smul_eq_mul]
  have hint_c : IntegrableOn (fun _ : ℝ => boseReg0 b) (Set.Ioc a b) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hsub : (∫ x in Set.Ioc a b, (boseReg0 b - boseReg0 x))
      = t * boseReg0 b - ∫ x in Set.Ioc a b, boseReg0 x := by
    rw [integral_sub hint_c hint_f, hconst]
  rw [hcell, ← hsub]
  have habs : |∫ x in Set.Ioc a b, (boseReg0 b - boseReg0 x)|
      ≤ ∫ x in Set.Ioc a b, |boseReg0 b - boseReg0 x| :=
    abs_integral_le_integral_abs
  have hmono : ∫ x in Set.Ioc a b, |boseReg0 b - boseReg0 x|
      ≤ ∫ _x in Set.Ioc a b, (∫ y in Set.Ioc a b, |boseReg0Deriv y|) := by
    apply setIntegral_mono_on
    · exact (hint_c.sub hint_f).abs
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · exact measurableSet_Ioc
    · exact hptwise
  have hconst2 : ∫ _x in Set.Ioc a b, (∫ y in Set.Ioc a b, |boseReg0Deriv y|)
      = t * ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
    rw [setIntegral_const, hvolr, smul_eq_mul]
  rw [hconst2] at hmono
  linarith

/-- **The Riemann-sum `O(1)` bound** (brick-22 engine):
`|Σ'_{k≥1} boseReg0(tk) − (−1/2)/t| ≤ ∫₀^∞ |boseReg0′|`. -/
theorem riemann_boseReg0_bound {t : ℝ} (ht : 0 < t) :
    |(∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) - (-(1:ℝ)/2) / t|
      ≤ ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
  classical
  set g : ℕ → ℝ := (fun k : ℕ => if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) with hgdef
  have hsamp := summable_boseReg0_samples ht
  have hshift_eq : ∀ k : ℕ, g (k + 1) = boseReg0 (t * ((k : ℝ) + 1)) := by
    intro k
    have hbeta : g (k + 1)
        = if k + 1 = 0 then (0:ℝ) else boseReg0 (t * (((k + 1 : ℕ)) : ℝ)) := rfl
    rw [hbeta, if_neg (Nat.succ_ne_zero k)]
    congr 1
    push_cast
    ring
  have hguard : Summable g := by
    rw [← summable_nat_add_iff 1]
    refine hsamp.congr fun k => ?_
    exact (hshift_eq k).symm
  have htsum_shift : ∑' k : ℕ, g k = ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)) := by
    rw [hguard.tsum_eq_zero_add]
    have hg0 : g 0 = 0 := rfl
    rw [hg0, zero_add]
    exact tsum_congr hshift_eq
  -- the two HasSums
  have hC : HasSum (fun k : ℕ => t * boseReg0 (t * ((k : ℝ) + 1)))
      (t * ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1))) :=
    hsamp.hasSum.mul_left t
  have hD := hasSum_cell_boseReg0 ht
  have hE := hC.sub hD
  have hVsum := hasSum_cell_absDeriv ht
  -- error comparison
  have herr : ∀ k : ℕ,
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|
        ≤ t * ∫ x in cell t k, |boseReg0Deriv x| := fun k => cell_error ht k
  have habs_summable : Summable (fun k : ℕ =>
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) herr (hVsum.summable.mul_left t)
  have hbound : (∑' k : ℕ,
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|)
        ≤ t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
    have h1 := habs_summable.tsum_le_tsum herr (hVsum.summable.mul_left t)
    have h2 : (∑' k : ℕ, t * ∫ x in cell t k, |boseReg0Deriv x|)
        = t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
      rw [tsum_mul_left, hVsum.tsum_eq]
    linarith
  have htri : |t * (∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)))
        - ∫ x in Set.Ioi 0, boseReg0 x|
      ≤ ∑' k : ℕ,
        |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x| := by
    rw [← hE.tsum_eq]
    have hnorm : |∑' k : ℕ,
        (t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x)|
        = ‖∑' k : ℕ,
        (t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x)‖ :=
      (Real.norm_eq_abs _).symm
    rw [hnorm]
    have hns : Summable (fun k : ℕ =>
        ‖t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x‖) := by
      refine habs_summable.congr fun k => ?_
      rw [Real.norm_eq_abs]
    exact le_trans (norm_tsum_le_tsum_norm hns)
      (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
  have hfinal : |t * (∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)))
        - ∫ x in Set.Ioi 0, boseReg0 x|
      ≤ t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := le_trans htri hbound
  -- conclude
  rw [htsum_shift]
  set S := ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)) with hSdef
  have hIval : ∫ x in Set.Ioi (0:ℝ), boseReg0 x = -(1 / 2 : ℝ) := integral_boseReg0_Ioi
  rw [hIval] at hfinal
  have hgoal_eq : S - (-(1:ℝ)/2) / t = (t * S - (-(1 / 2 : ℝ))) / t := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  nlinarith [hfinal]

/-- **M₀ weak asymptotics** (brick 22): `|M₀(t) − (π²/6)/t² + 1/(2t)| ≤ ∫₀^∞|boseReg0′|`. -/
theorem sigmaMoment_zero_asymp_weak {t : ℝ} (ht : 0 < t) :
    |sigmaMoment 0 t - (Real.pi ^ 2 / 6) / t ^ 2 + 1 / (2 * t)|
      ≤ ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
  classical
  have hML := sigmaMoment_zero_lambert ht
  -- summability of the two pieces
  have hsq0 : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    have hb0 : Summable (fun n : ℕ => (((n : ℝ) ^ (2:ℝ))⁻¹)) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hb1 := (summable_nat_add_iff 1).mpr hb0
    refine hb1.congr fun k => ?_
    rw [if_neg (Nat.succ_ne_zero k), show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  have hsq : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / (t * (k : ℝ)) ^ 2) := by
    have h2 := hsq0.mul_left (1 / t ^ 2)
    refine h2.congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
      field_simp
  have hreg : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_boseReg0_samples ht).congr fun k => ?_
    rw [if_neg (Nat.succ_ne_zero k)]
    congr 2
    push_cast
    ring
  -- termwise kernel split
  have hsplit : ∀ k : ℕ, (if k = 0 then (0:ℝ) else boseKernel (t * (k : ℝ)))
      = (if k = 0 then (0:ℝ) else 1 / (t * (k : ℝ)) ^ 2)
        + (if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk, boseKernel_eq_inv_sq_add_reg]
  have hsum_eq : (∑' k : ℕ, if k = 0 then (0:ℝ) else boseKernel (t * (k : ℝ)))
      = (Real.pi ^ 2 / 6) / t ^ 2
        + ∑' k : ℕ, (if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    rw [tsum_congr hsplit, hsq.tsum_add hreg, tsum_if_inv_sq_scaled ht.ne']
  rw [hML, hsum_eq]
  have harr : (Real.pi ^ 2 / 6) / t ^ 2
        + (∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ)))
        - (Real.pi ^ 2 / 6) / t ^ 2 + 1 / (2 * t)
      = (∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ)))
        - (-(1:ℝ)/2) / t := by
    field_simp
    ring
  rw [harr]
  exact riemann_boseReg0_bound ht

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: §6 the √n-cancellation in the second-order approximation

`kernelMassApprox2 n = (1/n)·M₀(t) + (1/n²)·M₁(t) − (C/(8n²√n))·M₂(t)` at `t = lam/√n` satisfies
`|kernelMassApprox2 n − 1| ≤ K/n` eventually: the three weak asymptotics give a leading `1`, the
`1/√n` terms cancel exactly (`mass_rate_sqrt_coeff_cancel`, `massLam_sq` i.e. `lam²=π²/6`), and all
remainders are `O(1/n)`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **√n-cancellation** (R8 §6): `|kernelMassApprox2 n − 1| ≤ K/n` eventually. -/
theorem kernelMassApprox2_cancel_sqrt_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMassApprox2 n - 1| ≤ K / (n : ℝ) := by
  set Z : ℝ := Real.pi ^ 2 / 6 with hZdef
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := massLam_pos
  have hlam2 : lam ^ 2 = Z := massLam_sq
  set I₀ : ℝ := ∫ x in Set.Ioi (0:ℝ), |boseReg0Deriv x| with hI0def
  have hI0nn : 0 ≤ I₀ := by
    rw [hI0def]; exact MeasureTheory.integral_nonneg (fun x => abs_nonneg _)
  set K₂ : ℝ := (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
    with hK2def
  have hK2nn : 0 ≤ K₂ := by rw [hK2def]; positivity
  refine ⟨I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1, ?_, ?_⟩
  · have hp1 : (0:ℝ) ≤ 388 / lam ^ 2 := by positivity
    have hp2 : (0:ℝ) ≤ C * K₂ / (8 * lam ^ 3) :=
      div_nonneg (mul_nonneg C_pos.le hK2nn) (by positivity)
    linarith [hI0nn, hp1, hp2]
  -- eventually n ≥ max(1, lam²) so that t = lam/√n ≤ 1 and n ≥ 1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    constructor
    · have : (1:ℕ) ≤ n := le_trans (le_max_left _ _) hn
      exact_mod_cast this
    · have h2 : (⌈lam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
        have : ⌈lam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hn
        exact_mod_cast this
      exact le_trans (Nat.le_ceil _) h2
  filter_upwards [hev] with n hn
  obtain ⟨hn1, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hs0]
    -- lam ≤ s = √n  ⟺ lam² ≤ n
    rw [← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  -- the three asymptotics
  have h0 := sigmaMoment_zero_asymp_weak ht0
  have h1 := sigmaMoment_one_asymp_weak ht0 ht1
  have h2 := sigmaMoment_two_asymp_weak ht0 ht1
  rw [← hI0def] at h0
  rw [← hZdef] at h0 h1 h2
  rw [← hK2def] at h2
  -- abbreviate the three remainders
  set R0 : ℝ := sigmaMoment 0 t - Z / t ^ 2 + 1 / (2 * t) with hR0def
  set R1 : ℝ := sigmaMoment 1 t - 2 * Z / t ^ 3 with hR1def
  set R2 : ℝ := sigmaMoment 2 t - 6 * Z / t ^ 4 with hR2def
  have hR0 : |R0| ≤ I₀ := h0
  have hR1 : |R1| ≤ 388 / t ^ 2 := h1
  have hR2 : |R2| ≤ K₂ / t ^ 3 := h2
  -- powers of t in terms of n
  have htne : t ≠ 0 := ht0.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hlamne : lam ≠ 0 := hlam0.ne'
  have ht2 : t ^ 2 = lam ^ 2 / (n : ℝ) := by rw [htdef, div_pow, ← hs2]
  have ht3 : t ^ 3 = lam ^ 3 / (s * (n : ℝ)) := by
    rw [htdef, div_pow, ← hs2]; field_simp
  have ht4 : t ^ 4 = lam ^ 4 / (n : ℝ) ^ 2 := by rw [htdef, div_pow, ← hs2]; ring
  -- express kernelMassApprox2 n
  have hCval : C = 2 * lam := by rw [hlamdef, massLam]; ring
  have hkey : kernelMassApprox2 n - 1
      = (1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1
        - (C / (8 * (n : ℝ) ^ 2 * s)) * R2
        + ((-(1 / (2 * lam)) + 2 * Z / lam ^ 3 - C * (6 * Z) / (8 * lam ^ 4)) / s) := by
    rw [kernelMassApprox2]
    simp only [← hsdef, ← htdef, ← hlamdef]
    have e0 : sigmaMoment 0 t = R0 + Z / t ^ 2 - 1 / (2 * t) := by rw [hR0def]; ring
    have e1 : sigmaMoment 1 t = R1 + 2 * Z / t ^ 3 := by rw [hR1def]; ring
    have e2 : sigmaMoment 2 t = R2 + 6 * Z / t ^ 4 := by rw [hR2def]; ring
    rw [e0, e1, e2, htdef, hCval, ← hlam2, ← hs2]
    field_simp
    ring
  rw [hkey]
  -- the √n-coefficient vanishes
  have hcancel : -(1 / (2 * lam)) + 2 * Z / lam ^ 3 - C * (6 * Z) / (8 * lam ^ 4) = 0 := by
    rw [hlamdef, hZdef]; exact mass_rate_sqrt_coeff_cancel
  rw [hcancel, zero_div, add_zero]
  -- bound the three remainder terms each by (·)/n
  have hb0 : |(1 / (n : ℝ)) * R0| ≤ I₀ / (n : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (n:ℝ))]
    rw [div_mul_eq_mul_div, one_mul]
    gcongr
  have hb1 : |(1 / (n : ℝ) ^ 2) * R1| ≤ (388 / lam ^ 2) / (n : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have : (1 / (n : ℝ) ^ 2) * (388 / t ^ 2) = (388 / lam ^ 2) / (n : ℝ) := by
      rw [ht2]; field_simp
    calc (1 / (n : ℝ) ^ 2) * |R1| ≤ (1 / (n : ℝ) ^ 2) * (388 / t ^ 2) :=
          mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ = (388 / lam ^ 2) / (n : ℝ) := this
  have hb2 : |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| ≤ (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := by
    have hCpos : 0 < C := C_pos
    rw [abs_mul, abs_of_pos (by positivity)]
    have heq : (C / (8 * (n : ℝ) ^ 2 * s)) * (K₂ / t ^ 3) = (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := by
      rw [ht3]; field_simp
    calc (C / (8 * (n : ℝ) ^ 2 * s)) * |R2|
        ≤ (C / (8 * (n : ℝ) ^ 2 * s)) * (K₂ / t ^ 3) :=
          mul_le_mul_of_nonneg_left hR2 (by positivity)
      _ = (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := heq
  -- assemble
  have htri : |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1 - (C / (8 * (n : ℝ) ^ 2 * s)) * R2|
      ≤ |(1 / (n : ℝ)) * R0| + |(1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
    calc |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1 - (C / (8 * (n : ℝ) ^ 2 * s)) * R2|
        ≤ |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      _ ≤ |(1 / (n : ℝ)) * R0| + |(1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
          gcongr
          exact abs_add_le _ _
  have hsum : I₀ / (n : ℝ) + (388 / lam ^ 2) / (n : ℝ) + (C * K₂ / (8 * lam ^ 3)) / (n : ℝ)
      ≤ (I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1) / (n : ℝ) := by
    have heq : (I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1) / (n : ℝ)
        = (I₀ / (n : ℝ) + (388 / lam ^ 2) / (n : ℝ) + (C * K₂ / (8 * lam ^ 3)) / (n : ℝ))
          + 1 / (n : ℝ) := by ring
    rw [heq]
    have h1n : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  linarith [htri, hb0, hb1, hb2, hsum]

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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop, |kernelMass n - 1| ≤ K / (n:ℝ) := by
  obtain ⟨K1, hK1, h1⟩ := kernelMass_sub_approx2
  obtain ⟨K2, hK2, h2⟩ := kernelMassApprox2_cancel_sqrt_term
  refine ⟨K1 + K2, by linarith, ?_⟩
  filter_upwards [h1, h2] with n hn1 hn2
  have hrw : kernelMass n - 1
      = (kernelMass n - kernelMassApprox2 n) + (kernelMassApprox2 n - 1) := by ring
  calc |kernelMass n - 1|
      = |(kernelMass n - kernelMassApprox2 n) + (kernelMassApprox2 n - 1)| := by rw [hrw]
    _ ≤ |kernelMass n - kernelMassApprox2 n| + |kernelMassApprox2 n - 1| := abs_add_le _ _
    _ ≤ K1 / (n:ℝ) + K2 / (n:ℝ) := by linarith [hn1, hn2]
    _ = (K1 + K2) / (n:ℝ) := by ring
