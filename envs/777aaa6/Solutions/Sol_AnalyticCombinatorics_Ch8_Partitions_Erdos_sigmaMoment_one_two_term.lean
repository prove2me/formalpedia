-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_one_two_term
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:08.656602+00:00
-- url     : https://prove2.me/submissions/bf81ec59-c52e-4da2-8c14-0fe5ade15195

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_boseReg0Deriv_bdd_near_zero
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the `M₂` Lambert identity by termwise differentiation

`M₂(t) = Σ_k k²·boseKernel3(tk)`, `boseKernel3(z) = e^{−z}(1+4e^{−z}+e^{−2z})/(1−e^{−z})⁴
= Σ_d d³e^{−dz}` — obtained by differentiating both sides of `sigmaMoment_one_lambert`
termwise on `Ioi (t/2)` via `hasDerivAt_tsum_of_isPreconnected`, then `HasDerivAt.unique`.
Mirror of `MassRateMomentOne`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_d d³ e^{−dz}` in closed form. -/
noncomputable def boseKernel3 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + 4 * Real.exp (-z) + Real.exp (-z) ^ 2) / (1 - Real.exp (-z)) ^ 4

/-- `boseKernel2` has derivative `−boseKernel3` on `(0,∞)` (quotient rule). -/
lemma boseKernel2_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel2 (-boseKernel3 z) z := by
  have hy1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd0 : (0:ℝ) < 1 - Real.exp (-z) := by linarith
  have hy : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-z)) z := by
    have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa using (Real.hasDerivAt_exp (-z)).comp z hinner
  -- numerator y(1+y)
  have hone : HasDerivAt (fun u : ℝ => 1 + Real.exp (-u)) (-Real.exp (-z)) z :=
    hy.const_add 1
  have hN := hy.mul hone
  -- denominator (1−y)³
  have hbase : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-z)) z := by
    simpa using hy.const_sub 1
  have hD := hbase.pow 3
  have hQ := hN.div hD (pow_ne_zero 3 hd0.ne')
  have hshape : boseKernel2
      = fun u : ℝ => Real.exp (-u) * (1 + Real.exp (-u)) / (1 - Real.exp (-u)) ^ 3 := rfl
  rw [hshape]
  convert hQ using 1
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
  rw [boseKernel3]
  field_simp
  ring

/-- `boseKernel3 ≥ 0` on `(0,∞)`. -/
lemma boseKernel3_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel3 z := by
  have h1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel3]
  positivity

/-- Tail comparison: `boseKernel3(z) ≤ 6e^{−z}/(1−e^{−a})⁴` for `z ≥ a > 0`. -/
lemma boseKernel3_le {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) :
    boseKernel3 z ≤ 6 * Real.exp (-z) / (1 - Real.exp (-a)) ^ 4 := by
  have hea : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hda : 0 < 1 - Real.exp (-a) := by linarith
  have hez : Real.exp (-z) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hdz : 0 < 1 - Real.exp (-z) := by linarith
  have hd_mono : 1 - Real.exp (-a) ≤ 1 - Real.exp (-z) := by linarith
  rw [boseKernel3]
  apply div_le_div₀ (by positivity)
  · have h2 : 1 + 4 * Real.exp (-z) + Real.exp (-z) ^ 2 ≤ 6 := by
      nlinarith [Real.exp_pos (-z), hez, hea]
    nlinarith [Real.exp_pos (-z)]
  · positivity
  · exact pow_le_pow_left₀ hda.le hd_mono 4

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the `reg3` near-zero bound (M₂ keystone input) — split certificate

`|boseKernel3 z − 6/z⁴| ≤ 3600` on `(0,1]`, degree-8 cancellation certificate, with the
heavy polynomial-coefficient bounds and the degree-28 `ring` identity factored into separate
lemmas (each under the per-declaration heartbeat budget).  Opus-authored (sympy-generated).
-/

noncomputable section

open Finset
open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 4000000
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyQ_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20| ≤ (1 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp13 : z ^ 13 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp14 : z ^ 14 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp15 : z ^ 15 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp16 : z ^ 16 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp17 : z ^ 17 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp18 : z ^ 18 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp19 : z ^ 19 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp20 : z ^ 20 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  have hn13 : (0:ℝ) ≤ z ^ 13 := by positivity
  have hn14 : (0:ℝ) ≤ z ^ 14 := by positivity
  have hn15 : (0:ℝ) ≤ z ^ 15 := by positivity
  have hn16 : (0:ℝ) ≤ z ^ 16 := by positivity
  have hn17 : (0:ℝ) ≤ z ^ 17 := by positivity
  have hn18 : (0:ℝ) ≤ z ^ 18 := by positivity
  have hn19 : (0:ℝ) ≤ z ^ 19 := by positivity
  have hn20 : (0:ℝ) ≤ z ^ 20 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA1_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21| ≤ (80 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp13 : z ^ 13 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp14 : z ^ 14 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp15 : z ^ 15 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp16 : z ^ 16 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp17 : z ^ 17 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp18 : z ^ 18 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp19 : z ^ 19 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp20 : z ^ 20 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp21 : z ^ 21 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  have hn13 : (0:ℝ) ≤ z ^ 13 := by positivity
  have hn14 : (0:ℝ) ≤ z ^ 14 := by positivity
  have hn15 : (0:ℝ) ≤ z ^ 15 := by positivity
  have hn16 : (0:ℝ) ≤ z ^ 16 := by positivity
  have hn17 : (0:ℝ) ≤ z ^ 17 := by positivity
  have hn18 : (0:ℝ) ≤ z ^ 18 := by positivity
  have hn19 : (0:ℝ) ≤ z ^ 19 := by positivity
  have hn20 : (0:ℝ) ≤ z ^ 20 := by positivity
  have hn21 : (0:ℝ) ≤ z ^ 21 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA2_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14| ≤ (95 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp13 : z ^ 13 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp14 : z ^ 14 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  have hn13 : (0:ℝ) ≤ z ^ 13 := by positivity
  have hn14 : (0:ℝ) ≤ z ^ 14 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA3_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7| ≤ (41 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hn1, hn2, hn3, hn4, hn5, hn6, hn7], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hn1, hn2, hn3, hn4, hn5, hn6, hn7]⟩

/-- Order-8 Taylor remainder for `w = 1−e^{−z}`: `|w − P₇(z)| ≤ z⁸` on `[0,1]`. -/
lemma w_sub_taylor7_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(1 - Real.exp (-z)) - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)| ≤ z ^ 8 := by
  have habs : |(-z)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hz0]; exact hz1
  have h := Real.exp_bound habs (n := 8) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 8, (-z) ^ i / (Nat.factorial i : ℝ)
      = 1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120 + z ^ 6 / 720 - z ^ 7 / 5040 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum] at h
  have habs8 : |(-z)| ^ 8 = z ^ 8 := by rw [abs_neg, abs_of_nonneg hz0]
  rw [habs8] at h
  have hc : (z : ℝ) ^ 8 * ((8 : ℕ).succ / ((Nat.factorial 8 : ℝ) * 8)) ≤ z ^ 8 := by
    have hz8 : (0:ℝ) ≤ z ^ 8 := by positivity
    have hcle : ((8 : ℕ).succ : ℝ) / ((Nat.factorial 8 : ℝ) * 8) ≤ 1 := by norm_num [Nat.factorial]
    nlinarith [hz8, hcle]
  have hrw : (1 - Real.exp (-z)) - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)
      = -(Real.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120
          + z ^ 6 / 720 - z ^ 7 / 5040)) := by ring
  rw [hrw, abs_neg]
  exact le_trans h hc

section
end

set_option maxHeartbeats 0 in
/-- The degree-8 numerator identity (pure `ring` in `(z,w)`). -/
lemma reg3_N3_identity (z w : ℝ) :
    z ^ 4 * (6 - 12 * w + 7 * w ^ 2 - w ^ 3) - 6 * w ^ 4
      = z ^ 8 * ((1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20) + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) * ((-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21)
        + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 2 * ((-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14)
        + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 3 * ((-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7)
        - 6 * (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 4 := by
  ring

/-- The rational form of `reg3` with `w = 1 - e^{-z}` written out. -/
lemma reg3_hreg_eq {z : ℝ} (hz0 : 0 < z) :
    boseKernel3 z - 6 / z ^ 4
      = (z ^ 4 * (6 - 12 * (1 - Real.exp (-z)) + 7 * (1 - Real.exp (-z)) ^ 2 - (1 - Real.exp (-z)) ^ 3)
          - 6 * (1 - Real.exp (-z)) ^ 4) / (z ^ 4 * (1 - Real.exp (-z)) ^ 4) := by
  have hexp1 : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hwd : (1 - Real.exp (-z)) ≠ 0 := (sub_pos.mpr hexp1).ne'
  rw [boseKernel3]
  field_simp
  ring

/-- Combining the certificate bounds, with the certificate polynomials kept abstract. -/
lemma reg3_combo_abstract {N z8 δ Q A1 A2 A3 : ℝ}
    (hN : N = z8 * Q + δ * A1 + δ ^ 2 * A2 + δ ^ 3 * A3 - 6 * δ ^ 4)
    (hz8 : 0 ≤ z8) (hz8le : z8 ≤ 1) (hδ : |δ| ≤ z8)
    (hQ : |Q| ≤ 1) (hA1 : |A1| ≤ 80) (hA2 : |A2| ≤ 95) (hA3 : |A3| ≤ 41) :
    |N| ≤ 223 * z8 := by
  subst hN
  have hδ0 : 0 ≤ |δ| := abs_nonneg δ
  have hd2 : |δ| ^ 2 ≤ z8 :=
    (pow_le_pow_left₀ hδ0 hδ 2).trans (pow_le_of_le_one hz8 hz8le (by norm_num))
  have hd3 : |δ| ^ 3 ≤ z8 :=
    (pow_le_pow_left₀ hδ0 hδ 3).trans (pow_le_of_le_one hz8 hz8le (by norm_num))
  have hd4 : |δ| ^ 4 ≤ z8 :=
    (pow_le_pow_left₀ hδ0 hδ 4).trans (pow_le_of_le_one hz8 hz8le (by norm_num))
  have e1 : |z8 * Q| ≤ z8 * 1 := by
    rw [abs_mul, abs_of_nonneg hz8]; exact mul_le_mul_of_nonneg_left hQ hz8
  have e2 : |δ * A1| ≤ z8 * 80 := by
    rw [abs_mul]; exact mul_le_mul hδ hA1 (abs_nonneg _) hz8
  have e3 : |δ ^ 2 * A2| ≤ z8 * 95 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul hd2 hA2 (abs_nonneg _) hz8
  have e4 : |δ ^ 3 * A3| ≤ z8 * 41 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul hd3 hA3 (abs_nonneg _) hz8
  have e5 : |6 * δ ^ 4| ≤ z8 * 6 := by
    rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]; linarith
  rw [abs_le] at e1 e2 e3 e4 e5 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-- Denominator lower bound from `z / 2 ≤ w`. -/
lemma reg3_den_bound {z w : ℝ} (hz : 0 < z) (hw : z / 2 ≤ w) : z ^ 8 / 16 ≤ z ^ 4 * w ^ 4 := by
  have h1 : (z / 2) ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ (by positivity) hw 4
  have h2 : z ^ 8 / 16 = z ^ 4 * (z / 2) ^ 4 := by ring
  rw [h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Final division step. -/
lemma reg3_final {N D z8 : ℝ} (h1 : |N| ≤ 223 * z8) (h2 : z8 / 16 ≤ D) (hD : 0 < D) :
    |N / D| ≤ 3600 := by
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]; linarith

/-- **`reg3` near-zero bound** (degree-8 certificate). -/
lemma reg3_bdd_near_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |boseKernel3 z - 6 / z ^ 4| ≤ 3600 := by
  have hexp1 : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hwpos : 0 < 1 - Real.exp (-z) := sub_pos.mpr hexp1
  have hwhalf : z / 2 ≤ 1 - Real.exp (-z) := by
    have h := one_sub_exp_neg_ge_half hz0 hz1; linarith
  rw [reg3_hreg_eq hz0]
  exact reg3_final
    (reg3_combo_abstract (reg3_N3_identity z (1 - Real.exp (-z))) (by positivity)
      (pow_le_one₀ hz0.le hz1) (w_sub_taylor7_bound hz0.le hz1) (reg3_polyQ_bound hz0.le hz1)
      (reg3_polyA1_bound hz0.le hz1) (reg3_polyA2_bound hz0.le hz1) (reg3_polyA3_bound hz0.le hz1))
    (reg3_den_bound hz0 hwhalf) (by positivity)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: `M₂` weak asymptotics

`|M₂(t) − 6(π²/6)/t⁴| ≤ K/t³` on `0 < t ≤ 1`.  Split `M₂ = Σ'_{k} k²·boseKernel3(tk)` via
`boseKernel3 z = 6/z⁴ + reg3(z)`: singular part sums (Basel) to `6(π²/6)/t⁴`, remainder
`Σ'_k k²·reg3(tk)` bounded by the weighted-decay keystone (`j=2`, `Cf=3600`, `Df=6`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `reg3` tail bound: `|boseKernel3 z − 6/z⁴| ≤ (6/(1−e^{−1})⁴)·e^{−z/2} + 6/z⁴` for `z > 1`. -/
lemma reg3_tail {z : ℝ} (hz1 : 1 < z) :
    |boseKernel3 z - 6 / z ^ 4|
      ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) + 6 / z ^ 4 := by
  have hzpos : 0 < z := by linarith
  have hb3nn : 0 ≤ boseKernel3 z := boseKernel3_nonneg hzpos
  have hle := boseKernel3_le (by norm_num : (0:ℝ) < 1) hz1.le
  have hexp_le : Real.exp (-z) ≤ Real.exp (-z / 2) := by
    apply Real.exp_le_exp.mpr; linarith [Real.exp_pos (-z)]
  have htri : |boseKernel3 z - 6 / z ^ 4| ≤ |boseKernel3 z| + |6 / z ^ 4| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  rw [abs_of_nonneg hb3nn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 / z ^ 4)] at htri
  have hDpos : (0:ℝ) < (1 - Real.exp (-1)) ^ 4 := by
    have he : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have hb : (0:ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  have hstep : boseKernel3 z ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) := by
    refine hle.trans ?_
    rw [show 6 * Real.exp (-z) / (1 - Real.exp (-1)) ^ 4
        = (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z) from by ring]
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  linarith [htri, hstep]

/-- Global `reg3` bound: `|reg3 z| ≤ B₃·e^{−z/2} + 3600/z⁴` for all `z > 0`. -/
lemma reg3_global_bound {z : ℝ} (hz : 0 < z) :
    |boseKernel3 z - 6 / z ^ 4|
      ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) + 3600 / z ^ 4 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := reg3_bdd_near_zero hz hz1
    have h2 : (3600:ℝ) ≤ 3600 / z ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      have : z ^ 4 ≤ 1 := pow_le_one₀ hz.le hz1
      nlinarith
    have h3 : (0:ℝ) ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) := by positivity
    linarith
  · have h1 := reg3_tail hz1
    have h2 : (6:ℝ) / z ^ 4 ≤ 3600 / z ^ 4 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
noncomputable section

open Filter Finset Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 1000000

private lemma pairwise_disjoint_Ioc_mul_nat_succ {t : ℝ} (ht : 0 ≤ t) :
    Pairwise (Disjoint on fun k : ℕ =>
      Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : i + 1 ≤ j := by omega
    have hreal : (((i + 1 : ℕ) : ℝ) ≤ (j : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((i + 1 : ℕ) : ℝ) ≤ t * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxi.2.trans hle) hxj.1
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((j + 1 : ℕ) : ℝ) ≤ t * (i : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxj.2.trans hle) hxi.1

private lemma iUnion_Ioc_mul_nat_succ_eq_Ioi {t : ℝ} (ht : 0 < t) :
    (⋃ k : ℕ, Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) =
      Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    have hk_nonneg : 0 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.zero_le k)
    exact (mul_nonneg ht.le hk_nonneg).trans_lt hk.1
  · intro hx
    let y : ℝ := x / t
    have hy_pos : 0 < y := by
      dsimp [y]
      exact div_pos hx ht
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := by
      have : 0 < Nat.ceil y := (Nat.ceil_pos (a := y)).mpr hy_pos
      simpa [n] using this
    let k : ℕ := n - 1
    have hk_succ : k + 1 = n := by
      dsimp [k]
      omega
    have hlt_nat : k < Nat.ceil y := by
      dsimp [k, n]
      omega
    have hk_lt_y : ((k : ℕ) : ℝ) < y :=
      (Nat.lt_ceil (a := y) (n := k)).mp hlt_nat
    have hy_le_n : y ≤ (n : ℝ) := by
      have hnn : Nat.ceil y ≤ n := by
        simp [n]
      exact (Nat.ceil_le (a := y) (n := n)).mp hnn
    have hy_le_succ : y ≤ (((k + 1 : ℕ) : ℝ)) := by
      simpa [hk_succ] using hy_le_n
    have hmul : t * y = x := by
      dsimp [y]
      field_simp [ht.ne']
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [← hmul]
    constructor
    · exact mul_lt_mul_of_pos_left hk_lt_y ht
    · exact mul_le_mul_of_nonneg_left hy_le_succ ht.le

theorem riemann_sum_Ioi_sub_integral_bound
    {f f' : ℝ → ℝ} {M η : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hf'int : IntegrableOn f' (Set.Ioi 0))
    (hfint : IntegrableOn f (Set.Ioi 0))
    (hbdd : ∀ x : ℝ, 0 < x → x ≤ η → |f x| ≤ M) :
    ∀ t : ℝ, 0 < t → t < η →
      |(∑' k : ℕ, if k = 0 then 0 else f (t * (k : ℝ)))
        - (1 / t) * ∫ x in Set.Ioi 0, f x| ≤
          (∫ x in Set.Ioi 0, |f' x|) + M := by
  intro t ht htη
  classical

  let a : ℕ → ℝ := fun k : ℕ => t * (k : ℝ)
  let b : ℕ → ℝ := fun k : ℕ => t * ((k + 1 : ℕ) : ℝ)
  let cell : ℕ → Set ℝ := fun k : ℕ => Set.Ioc (a k) (b k)
  let A : ℕ → ℝ := fun k : ℕ => if k = 0 then 0 else f (a k)
  let B : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, f x
  let D : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, |f' x|
  let G : ℕ → ℝ := fun k : ℕ => (if k = 0 then M * t else 0) + t * D k

  have hUnion : (⋃ k : ℕ, cell k) = Set.Ioi (0 : ℝ) := by
    simpa [cell, a, b] using iUnion_Ioc_mul_nat_succ_eq_Ioi (t := t) ht
  have hmeas : ∀ k : ℕ, MeasurableSet (cell k) := by
    intro k
    simp [cell, a, b]
  have hpair : Pairwise (Disjoint on cell) := by
    simpa [cell, a, b] using pairwise_disjoint_Ioc_mul_nat_succ (t := t) ht.le

  have hf'int_abs : IntegrableOn (fun x : ℝ => |f' x|) (Set.Ioi (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using hf'int.norm

  have hcells_f : HasSum B (∫ x in Set.Ioi (0 : ℝ), f x) := by
    have h_int_union : IntegrableOn f (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hfint
    simpa [B, hUnion] using
      (hasSum_integral_iUnion (μ := volume) (f := f) hmeas hpair h_int_union)

  have hcells_D : HasSum D (∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h_int_union :
        IntegrableOn (fun x : ℝ => |f' x|) (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hf'int_abs
    simpa [D, hUnion] using
      (hasSum_integral_iUnion
        (μ := volume) (f := fun x : ℝ => |f' x|) hmeas hpair h_int_union)

  have hD_nonneg : ∀ k : ℕ, 0 ≤ D k := by
    intro k
    dsimp [D]
    exact integral_nonneg (fun x : ℝ => abs_nonneg (f' x))

  have hab_ab : ∀ k : ℕ, a k ≤ b k := by
    intro k
    dsimp [a, b]
    have hnat : k ≤ k + 1 := Nat.le_succ k
    have hreal : ((k : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hreal ht.le

  have hpos_a : ∀ k : ℕ, k ≠ 0 → 0 < a k := by
    intro k hk
    dsimp [a]
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    exact mul_pos ht hkpos

  have hpoint :
      ∀ (k : ℕ), k ≠ 0 → ∀ x : ℝ, x ∈ cell k → |f x - f (a k)| ≤ D k := by
    intro k hk x hx
    have ha_pos : 0 < a k := hpos_a k hk
    have hax : a k ≤ x := le_of_lt hx.1
    have hxb : x ≤ b k := hx.2
    have hderiv' : ∀ y ∈ Set.uIcc (a k) x, HasDerivAt f (f' y) y := by
      intro y hy
      have hy' : y ∈ Set.Icc (a k) x := by
        simpa [Set.uIcc_of_le hax] using hy
      exact hderiv y (ha_pos.trans_le hy'.1)
    have hint : IntervalIntegrable f' volume (a k) x := by
      have hsub : Set.uIcc (a k) x ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) x := by
          simpa [Set.uIcc_of_le hax] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := f) (f' := f') (a := a k) (b := x) hderiv' hint
    have hnorm1 : |f x - f (a k)| ≤ ∫ u in a k..x, |f' u| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs
        (μ := volume) (f := f') hax
    have hint_ab : IntervalIntegrable f' volume (a k) (b k) := by
      have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) (b k) := by
          simpa [Set.uIcc_of_le (hab_ab k)] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hint_abs_ab :
        IntervalIntegrable (fun u : ℝ => |f' u|) volume (a k) (b k) :=
      hint_ab.abs
    have hmono :
        ∫ u in a k..x, |f' u| ≤ ∫ u in a k..b k, |f' u| := by
      exact intervalIntegral.integral_mono_interval
        (μ := volume) (f := fun u : ℝ => |f' u|)
        (a := a k) (b := x) (c := a k) (d := b k)
        le_rfl hax hxb
        (Eventually.of_forall (fun u : ℝ => abs_nonneg (f' u)))
        hint_abs_ab
    have hright_eq : ∫ u in a k..b k, |f' u| = D k := by
      rw [intervalIntegral.integral_of_le (hab_ab k)]
    exact hnorm1.trans (hmono.trans_eq hright_eq)

  have hhead_interval : |∫ x in (0 : ℝ)..t, f x| ≤ M * t := by
    have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖f x‖ ≤ M := by
      intro x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) t := by
        simpa [Set.uIoc_of_le ht.le] using hx
      simpa [Real.norm_eq_abs] using hbdd x hx'.1 (hx'.2.trans htη.le)
    have hnorm :
        ‖∫ x in (0 : ℝ)..t, f x‖ ≤ M * |t - (0 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := M) (f := f) hbound
    simpa [Real.norm_eq_abs, abs_of_pos ht] using hnorm

  have hcell_error : ∀ k : ℕ, |t * A k - B k| ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hB0_eq : B 0 = ∫ x in (0 : ℝ)..t, f x := by
        dsimp [B, cell, a, b]
        rw [intervalIntegral.integral_of_le ht.le]
        simp
      calc
        |t * A 0 - B 0| = |B 0| := by
          simp [A]
        _ = |∫ x in (0 : ℝ)..t, f x| := by
          rw [hB0_eq]
        _ ≤ M * t := hhead_interval
        _ ≤ M * t + t * D 0 := by
          exact le_add_of_nonneg_right (mul_nonneg ht.le (hD_nonneg 0))
        _ = G 0 := by
          simp [G]
    · have hB_eq : B k = ∫ x in a k..b k, f x := by
        dsimp [B, cell]
        rw [intervalIntegral.integral_of_le (hab_ab k)]
      have hconst : (∫ x in a k..b k, A k) = t * A k := by
        rw [intervalIntegral.integral_const]
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba]
        simp [smul_eq_mul]
      have hf_interval : IntervalIntegrable f volume (a k) (b k) := by
        have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
          intro y hy
          have hy' : y ∈ Set.Icc (a k) (b k) := by
            simpa [Set.uIcc_of_le (hab_ab k)] using hy
          exact (hpos_a k hk).trans_le hy'.1
        exact (hfint.mono_set hsub).intervalIntegrable
      have hconst_int :
          IntervalIntegrable (fun _ : ℝ => A k) volume (a k) (b k) :=
        intervalIntegrable_const
      have hdiff :
          (∫ x in a k..b k, f x - A k) =
            (∫ x in a k..b k, f x) - (∫ x in a k..b k, A k) := by
        exact intervalIntegral.integral_sub hf_interval hconst_int
      have hbound_int : ∀ x ∈ Set.uIoc (a k) (b k), ‖f x - A k‖ ≤ D k := by
        intro x hx
        have hxcell : x ∈ cell k := by
          simpa [cell, Set.uIoc_of_le (hab_ab k)] using hx
        simpa [A, hk, Real.norm_eq_abs] using hpoint k hk x hxcell
      have hnorm_bound :
          ‖∫ x in a k..b k, f x - A k‖ ≤ D k * |b k - a k| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a k) (b := b k) (C := D k)
          (f := fun x : ℝ => f x - A k) hbound_int
      have hrepr :
          t * A k - B k = - (∫ x in a k..b k, f x - A k) := by
        rw [hB_eq, ← hconst, hdiff]
        ring
      have habs : |b k - a k| = t := by
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba, abs_of_pos ht]
      have hmain : |t * A k - B k| ≤ t * D k := by
        calc
          |t * A k - B k| = ‖∫ x in a k..b k, f x - A k‖ := by
            rw [hrepr, Real.norm_eq_abs, abs_neg]
          _ ≤ D k * |b k - a k| := hnorm_bound
          _ = t * D k := by
            rw [habs]
            ring
      calc
        |t * A k - B k| ≤ t * D k := hmain
        _ = G k := by
          simp [G, hk]

  have hsumm_B : Summable B := hcells_f.summable
  have hhas_tD :
      HasSum (fun k : ℕ => t * D k)
        (t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := HasSum.const_smul t hcells_D
    simpa [smul_eq_mul] using h
  have hsingle : HasSum (fun k : ℕ => if k = 0 then M * t else 0) (M * t) :=
    hasSum_ite_eq (0 : ℕ) (M * t)
  have hhas_G :
      HasSum G (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := hsingle.add hhas_tD
    simpa [G, add_comm, add_left_comm, add_assoc] using h

  have hsumm_abs_error : Summable (fun k : ℕ => |t * A k - B k|) :=
    Summable.of_nonneg_of_le
      (fun k : ℕ => abs_nonneg (t * A k - B k))
      (fun k : ℕ => hcell_error k)
      hhas_G.summable
  have hsumm_error : Summable (fun k : ℕ => t * A k - B k) :=
    Summable.of_abs hsumm_abs_error

  have hsumm_tA : Summable (fun k : ℕ => t * A k) := by
    have h := hsumm_error.add hsumm_B
    refine h.congr ?_
    intro k
    ring

  have hsumm_A : Summable A := by
    have h := Summable.const_smul (1 / t) hsumm_tA
    refine h.congr ?_
    intro k
    change (1 / t) * (t * A k) = A k
    field_simp [ht.ne']

  have hhas_tA :
      HasSum (fun k : ℕ => t * A k) (t * (∑' k : ℕ, A k)) := by
    have h := HasSum.const_smul t hsumm_A.hasSum
    simpa [smul_eq_mul] using h

  have hhas_error :
      HasSum (fun k : ℕ => t * A k - B k)
        (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) :=
    hhas_tA.sub hcells_f

  have herror_eq :
      (∑' k : ℕ, (t * A k - B k)) =
        t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x :=
    HasSum.tsum_eq hhas_error

  have hsum_abs_has :
      HasSum (fun k : ℕ => |t * A k - B k|)
        (∑' k : ℕ, |t * A k - B k|) :=
    hsumm_abs_error.hasSum

  have habs_tsum :
      |∑' k : ℕ, (t * A k - B k)|
        ≤ ∑' k : ℕ, |t * A k - B k| := by
    have hupper :
        (∑' k : ℕ, (t * A k - B k))
          ≤ ∑' k : ℕ, |t * A k - B k| := by
      exact hasSum_le
        (fun k : ℕ => le_abs_self (t * A k - B k))
        hsumm_error.hasSum hsum_abs_has
    have hlower :
        -(∑' k : ℕ, |t * A k - B k|)
          ≤ ∑' k : ℕ, (t * A k - B k) := by
      have hneg :
          HasSum (fun k : ℕ => - |t * A k - B k|)
            (-(∑' k : ℕ, |t * A k - B k|)) :=
        hsum_abs_has.neg
      exact hasSum_le
        (fun k : ℕ => neg_abs_le (t * A k - B k))
        hneg hsumm_error.hasSum
    exact abs_le.mpr ⟨hlower, hupper⟩

  have habs_le_G :
      (∑' k : ℕ, |t * A k - B k|)
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    exact hasSum_le
      (fun k : ℕ => hcell_error k)
      hsum_abs_has hhas_G

  have hscaled :
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    calc
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
          = |∑' k : ℕ, (t * A k - B k)| := by
            rw [← herror_eq]
      _ ≤ ∑' k : ℕ, |t * A k - B k| := habs_tsum
      _ ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := habs_le_G

  have htinv_pos : 0 < 1 / t := one_div_pos.mpr ht

  change
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x| ≤
      (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M

  calc
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x|
        = (1 / t) *
            |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x| := by
          have hscale :
              (∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x =
                (1 / t) *
                  (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) := by
            field_simp [ht.ne']
          rw [hscale, abs_mul, abs_of_pos htinv_pos]
    _ ≤ (1 / t) *
          (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) :=
          mul_le_mul_of_nonneg_left hscaled htinv_pos.le
    _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
          calc
            (1 / t) * (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|)
                = (1 / t) *
                    (t * (M + ∫ x in Set.Ioi (0 : ℝ), |f' x|)) := by
                  ring
            _ = M + ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
                  field_simp [ht.ne']
            _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
                  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: the **two-term** moment-one asymptotic

The weak version (`sigmaMoment_one_asymp_weak`) gives only the leading term
`M₁(t) = 2(π²/6)/t³ + O(1/t²)`.  Here we extract the next order:

  `M₁(t) = 2(π²/6)/t³ − 1/(2t²) + O(1/t)`,  i.e.  `|M₁(t) − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t`.

The `−1/(2t²)` term is **not** a pointwise singularity of `boseKernel2`; it is the
Riemann-sum main term of the regularized derivative.  Writing
`M₁(t) = 2(π²/6)/t³ − Σ_{k≥1} k·boseReg0′(tk)` (the weak split), the remainder sum is
`(1/t)·Σ_{k≥1} G(tk)` with `G(x) = x·boseReg0′(x)`, and the general Riemann estimate
(`riemann_sum_Ioi_sub_integral_bound`) gives `Σ_{k≥1} G(tk) = (1/t)·∫₀^∞ G + O(1)`.
The integral is `∫₀^∞ x·boseReg0′(x) dx = 1/2`, computed via `G = (x·boseReg0)′ − boseReg0`
and `∫₀^∞ boseReg0 = −1/2` with vanishing boundary terms.  Hence
`Σ_{k≥1} k·boseReg0′(tk) = 1/(2t²) + O(1/t)`.  Opus-authored (ChatGPT R14 route, repo-verified).
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `G(x) = x · boseReg0′(x)`: the integrand whose Riemann sum carries the `−1/(2t²)` term. -/
noncomputable def Gw (x : ℝ) : ℝ := x * boseReg0Deriv x

/-- The derivative `G′(x) = boseReg0′(x) + x·(boseKernel3 x − 6/x⁴)`. -/
noncomputable def GwDeriv (x : ℝ) : ℝ :=
  boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4)

/-- Auxiliary integrability: `x·e^{−b x}` is integrable on `(1,∞)` for `b > 0`
(it is `O(e^{−(b/2)x})` at `∞`). -/
lemma id_mul_exp_neg_integrableOn_Ioi1 {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-b * x)) (Set.Ioi (1:ℝ)) := by
  apply integrable_of_isBigO_exp_neg (b := b / 2) (by positivity)
  · exact (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn
  · -- `x e^{−b x} =o e^{−(b/2) x}` ⟹ `=O`
    have hlit : (fun x : ℝ => x * Real.exp (-b * x))
        =o[atTop] (fun x : ℝ => Real.exp (-(b / 2) * x)) := by
      rw [Asymptotics.isLittleO_iff_tendsto (fun x hx => absurd hx (Real.exp_ne_zero _))]
      have hker := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (b / 2) (by positivity)
      refine hker.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [Real.rpow_one, eq_div_iff (Real.exp_ne_zero _), mul_assoc, ← Real.exp_add,
        show -(b / 2) * x + -(b / 2) * x = -b * x from by ring]
    exact hlit.isBigO

/-- `Gw` is globally measurable. -/
lemma Gw_measurable : Measurable Gw := by
  unfold Gw
  exact measurable_id.mul boseReg0Deriv_measurable

/-- `GwDeriv` is globally measurable. -/
lemma GwDeriv_measurable : Measurable GwDeriv := by
  unfold GwDeriv boseReg0Deriv boseKernel3
  measurability

/-- `|Gw x| ≤ 32` on `(0,1]`. -/
lemma Gw_bdd_unit {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : |Gw x| ≤ 32 := by
  rw [Gw, abs_mul, abs_of_pos hx0]
  have hb := boseReg0Deriv_bdd_near_zero hx0 hx1
  nlinarith [abs_nonneg (boseReg0Deriv x), hb, hx0.le, hx1]

/-- Integrability of `Gw` on `(0,1]`. -/
lemma Gw_integrableOn_Ioc01 : IntegrableOn Gw (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 32)
  · rw [Real.volume_Ioc]; norm_num
  · exact Gw_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact Gw_bdd_unit hx.1 hx.2

/-- Integrability of `Gw` on `(1,∞)`: dominated by `16·(x e^{−x/2}) + 2·(1/x²)`. -/
lemma Gw_integrableOn_Ioi1 : IntegrableOn Gw (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have hg1 : IntegrableOn (fun x : ℝ => 16 * (x * Real.exp (-(1/2) * x))) (Set.Ioi 1) :=
    (id_mul_exp_neg_integrableOn_Ioi1 (by norm_num : (0:ℝ) < 1/2)).const_mul 16
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (2 : ℝ)
  have hg := hg1.add hg2'
  apply Integrable.mono' hg Gw_measurable.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, Gw, abs_mul]
  have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
  rw [abs_of_pos hxpos]
  have hb := boseReg0Deriv_tail_bound hx.le
  -- x·|bRD x| ≤ x·(16 e^{−x/2} + 2/x³) = 16·(x e^{−x/2}) + 2·(1/x²)
  have hxnn : (0:ℝ) ≤ x := hxpos.le
  have hstep : x * |boseReg0Deriv x| ≤ x * (16 * Real.exp (-x / 2) + 2 / x ^ 3) :=
    mul_le_mul_of_nonneg_left hb hxnn
  have hrw : x * (16 * Real.exp (-x / 2) + 2 / x ^ 3)
      = 16 * (x * Real.exp (-(1/2) * x)) + 2 * (1 / x ^ 2) := by
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hxpos.ne'
    field_simp
  simp only [Pi.add_apply]
  rw [← hrw]
  exact hstep

/-- **Integrability of `Gw` on `(0,∞)`.** -/
lemma Gw_integrable_Ioi : IntegrableOn Gw (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact Gw_integrableOn_Ioc01.union Gw_integrableOn_Ioi1

/-- `|GwDeriv x| ≤ 3632` on `(0,1]`. -/
lemma GwDeriv_bdd_unit {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : |GwDeriv x| ≤ 3632 := by
  rw [GwDeriv]
  have hbrd := boseReg0Deriv_bdd_near_zero hx0 hx1
  have hreg := reg3_bdd_near_zero hx0 hx1
  have hxr : |x * (boseKernel3 x - 6 / x ^ 4)| ≤ 3600 := by
    rw [abs_mul, abs_of_pos hx0]
    nlinarith [abs_nonneg (boseKernel3 x - 6 / x ^ 4), hreg, hx0.le, hx1]
  calc |boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4)|
      ≤ |boseReg0Deriv x| + |x * (boseKernel3 x - 6 / x ^ 4)| := abs_add_le _ _
    _ ≤ 32 + 3600 := by linarith
    _ = 3632 := by norm_num

/-- Integrability of `GwDeriv` on `(0,1]`. -/
lemma GwDeriv_integrableOn_Ioc01 : IntegrableOn GwDeriv (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 3632)
  · rw [Real.volume_Ioc]; norm_num
  · exact GwDeriv_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact GwDeriv_bdd_unit hx.1 hx.2

/-- Integrability of `x·(boseKernel3 x − 6/x⁴)` on `(1,∞)`. -/
lemma id_mul_reg3_integrableOn_Ioi1 :
    IntegrableOn (fun x : ℝ => x * (boseKernel3 x - 6 / x ^ 4)) (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  set C : ℝ := 6 / (1 - Real.exp (-1)) ^ 4 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have hpos : (0:ℝ) < 1 - Real.exp (-1) := by
      have h := Real.exp_lt_one_iff.mpr (show (-1:ℝ) < 0 by norm_num); linarith
    exact div_pos (by norm_num) (pow_pos hpos 4)
  have hg1 : IntegrableOn (fun x : ℝ => C * (x * Real.exp (-(1/2) * x))) (Set.Ioi 1) :=
    (id_mul_exp_neg_integrableOn_Ioi1 (by norm_num : (0:ℝ) < 1/2)).const_mul C
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 3) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (3600 : ℝ)
  have hg := hg1.add hg2'
  have hmeasfun : Measurable (fun x : ℝ => x * (boseKernel3 x - 6 / x ^ 4)) := by
    have h3 : Measurable boseKernel3 := by unfold boseKernel3; measurability
    exact measurable_id.mul (h3.sub ((measurable_const).div (measurable_id.pow_const 4)))
  apply Integrable.mono' hg hmeasfun.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
  rw [abs_of_pos hxpos]
  have hreg := reg3_global_bound hxpos
  -- |reg3 x| ≤ C e^{−x/2} + 3600/x⁴
  have hstep : x * |boseKernel3 x - 6 / x ^ 4|
      ≤ x * (C * Real.exp (-x / 2) + 3600 / x ^ 4) :=
    mul_le_mul_of_nonneg_left (by rw [hCdef]; exact hreg) hxpos.le
  have hrw : x * (C * Real.exp (-x / 2) + 3600 / x ^ 4)
      = C * (x * Real.exp (-(1/2) * x)) + 3600 * (1 / x ^ 3) := by
    have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hxpos.ne'
    field_simp
  simp only [Pi.add_apply]
  rw [← hrw]
  exact hstep

/-- Integrability of `GwDeriv` on `(1,∞)`. -/
lemma GwDeriv_integrableOn_Ioi1 : IntegrableOn GwDeriv (Set.Ioi 1) := by
  have h := boseReg0Deriv_integrableOn_Ioi1.add id_mul_reg3_integrableOn_Ioi1
  simpa only [GwDeriv] using h

/-- **Integrability of `GwDeriv` on `(0,∞)`.** -/
lemma GwDeriv_integrable_Ioi : IntegrableOn GwDeriv (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact GwDeriv_integrableOn_Ioc01.union GwDeriv_integrableOn_Ioi1

/-- The derivative `boseReg0′` itself: `boseReg0′′(x) = boseKernel3 x − 6/x⁴`. -/
lemma boseReg0Deriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseReg0Deriv (boseKernel3 x - 6 / x ^ 4) x := by
  -- `boseReg0Deriv y = 2/y³ − boseKernel2 y` near `x`; differentiate that.
  have hcube : HasDerivAt (fun y : ℝ => 2 / y ^ 3) (-6 / x ^ 4) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 3) ((3:ℕ) * x ^ (3 - 1)) x := hasDerivAt_pow 3 x
    have h2 := h1.inv (pow_ne_zero 3 hx.ne')
    have h3 := h2.const_mul (2:ℝ)
    have heq : (2:ℝ) * (-((3:ℕ) * x ^ (3 - 1)) / (x ^ 3) ^ 2) = -6 / x ^ 4 := by
      push_cast; field_simp; ring
    rw [heq] at h3
    convert h3 using 2 with y
  have hk2 : HasDerivAt boseKernel2 (-boseKernel3 x) x := boseKernel2_hasDerivAt hx
  have hsub := hcube.sub hk2
  have hval : (-6 / x ^ 4 - (-boseKernel3 x)) = boseKernel3 x - 6 / x ^ 4 := by ring
  rw [hval] at hsub
  have hev : boseReg0Deriv =ᶠ[𝓝 x] (fun y => 2 / y ^ 3 - boseKernel2 y) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
    have hk := boseKernel2_eq_inv_cube_sub_deriv hy
    linarith [hk]
  exact hsub.congr_of_eventuallyEq hev

/-- `Gw` has derivative `GwDeriv` on `(0,∞)`. -/
lemma Gw_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt Gw (GwDeriv x) x := by
  have hbase := (hasDerivAt_id x).mul (boseReg0Deriv_hasDerivAt hx)
  simp only [id_eq, one_mul] at hbase
  have hval : boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4) = GwDeriv x := by rw [GwDeriv]
  rw [hval] at hbase
  exact hbase

/-- The improper-FTC auxiliary `H(x) = x·boseReg0(x)` tends to `0` at `∞`. -/
lemma id_mul_boseReg0_tendsto_atTop :
    Tendsto (fun x : ℝ => x * boseReg0 x) atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖x * boseReg0 x‖ ≤ 4 * (x * Real.exp (-x)) + 1 / x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hxpos]
    have hb := boseReg0_tail_bound hx
    have hstep : x * |boseReg0 x| ≤ x * (4 * Real.exp (-x) + 1 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hb hxpos.le
    have hrw : x * (4 * Real.exp (-x) + 1 / x ^ 2) = 4 * (x * Real.exp (-x)) + 1 / x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hxpos.ne'
      field_simp
    rw [hrw] at hstep
    exact hstep
  have hlim : Tendsto (fun x : ℝ => 4 * (x * Real.exp (-x)) + 1 / x) atTop (𝓝 0) := by
    have ht1 : Tendsto (fun x : ℝ => 4 * (x * Real.exp (-x))) atTop (𝓝 0) := by
      have hk := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have hk' : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
        refine hk.congr (fun x => ?_); rw [pow_one]
      have := hk'.const_mul (4:ℝ)
      simpa using this
    have ht2 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa using ht1.add ht2
  exact squeeze_zero_norm' hbound hlim

/-- **`∫_{(0,∞)} Gw = 1/2`.** -/
theorem integral_Gw_Ioi : ∫ x in Set.Ioi (0:ℝ), Gw x = 1 / 2 := by
  -- `H = (·)·boseReg0` has derivative `boseReg0 + Gw`, `H(0) = 0`, `H → 0`.
  have hcontW : ContinuousWithinAt (fun x : ℝ => x * boseReg0 x) (Set.Ici 0) 0 := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[Set.Ici 0] (0:ℝ),
        ‖x * boseReg0 x‖ ≤ 4 * |x| := by
      have hmem : Set.Iic (1:ℝ) ∈ 𝓝[Set.Ici 0] (0:ℝ) :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
      filter_upwards [hmem, self_mem_nhdsWithin] with x hx1 hx0
      have hx0' : (0:ℝ) ≤ x := hx0
      have hx1' : x ≤ 1 := hx1
      rw [Real.norm_eq_abs, abs_mul]
      rcases eq_or_lt_of_le hx0' with hx | hx
      · simp [← hx]
      · have hb := boseReg0_bdd_near_zero hx hx1'
        have hxabs : |x| ≤ 1 := by rw [abs_of_pos hx]; exact hx1'
        nlinarith [abs_nonneg x, abs_nonneg (boseReg0 x), hb, hxabs]
    have hlim : Tendsto (fun x : ℝ => 4 * |x|) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) := by
      have habs : Tendsto (fun x : ℝ => |x|) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) := by
        have := (continuous_abs.tendsto (0:ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ici (0:ℝ)))
        simpa using this
      simpa using habs.const_mul (4:ℝ)
    have key : Tendsto (fun x : ℝ => x * boseReg0 x) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) :=
      squeeze_zero_norm' hbound hlim
    have hH0 : (fun x : ℝ => x * boseReg0 x) (0:ℝ) = 0 := by simp
    show Tendsto (fun x : ℝ => x * boseReg0 x) (𝓝[Set.Ici 0] (0:ℝ))
      (𝓝 ((fun x : ℝ => x * boseReg0 x) (0:ℝ)))
    rw [hH0]; exact key
  have hderivW : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x : ℝ => x * boseReg0 x)
      (boseReg0 x + Gw x) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hb := (hasDerivAt_id x).mul (boseReg0_hasDerivAt hx')
    simp only [id_eq, one_mul] at hb
    have hval : boseReg0 x + x * boseReg0Deriv x = boseReg0 x + Gw x := by rw [Gw]
    rw [hval] at hb
    exact hb
  have hint : IntegrableOn (fun x : ℝ => boseReg0 x + Gw x) (Set.Ioi 0) :=
    boseReg0_integrable_Ioi.add Gw_integrable_Ioi
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcontW hderivW hint id_mul_boseReg0_tendsto_atTop
  -- `∫(boseReg0 + Gw) = 0 − H 0 = 0`
  have hzero : ∫ x in Set.Ioi (0:ℝ), (boseReg0 x + Gw x) = 0 := by rw [hftc]; simp
  -- split the integral
  have hsplit : ∫ x in Set.Ioi (0:ℝ), (boseReg0 x + Gw x)
      = (∫ x in Set.Ioi (0:ℝ), boseReg0 x) + ∫ x in Set.Ioi (0:ℝ), Gw x :=
    MeasureTheory.integral_add boseReg0_integrable_Ioi Gw_integrable_Ioi
  rw [hsplit, integral_boseReg0_Ioi] at hzero
  linarith [hzero]

/-- The Riemann-sum estimate for `G`: `|Σ_{k≥1} G(tk) − 1/(2t)| ≤ K` with
`K = ∫_{(0,∞)}|GwDeriv| + 32`, for `0 < t < 1`. -/
theorem riemann_Gw_bound :
    ∀ t : ℝ, 0 < t → t < 1 →
      |(∑' k : ℕ, if k = 0 then 0 else Gw (t * (k : ℝ)))
        - (1 / t) * (1 / 2)| ≤ (∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32 := by
  have hbase := riemann_sum_Ioi_sub_integral_bound
    (f := Gw) (f' := GwDeriv) (M := 32) (η := 1)
    (by norm_num) (by norm_num)
    (fun x hx => Gw_hasDerivAt hx)
    GwDeriv_integrable_Ioi Gw_integrable_Ioi
    (fun x hx0 hx1 => Gw_bdd_unit hx0 hx1)
  intro t ht ht1
  have h := hbase t ht ht1
  rwa [integral_Gw_Ioi] at h

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1600000
open Filter MeasureTheory Set
open scoped Topology
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t < 1 →
      |sigmaMoment 1 t - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))| ≤ K / t := by
  classical
  refine ⟨(∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32, by positivity, ?_⟩
  intro t ht ht1
  -- the weak decomposition: `M₁ = 2(π²/6)/t³ − Σ hrem`, `hrem = guarded k·boseReg0′(tk)`
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) * boseReg0Deriv (t * (k : ℝ)) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (2 / t ^ 3) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  have hML := sigmaMoment_one_lambert ht
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absDeriv ht
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
      have htne : t ≠ 0 := ht.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
  have hM1_eq : sigmaMoment 1 t = (∑' k, hmain k) - (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_sub hrem_summ]
  have hmain_eq : (∑' k, hmain k) = 2 * (Real.pi ^ 2 / 6) / t ^ 3 := by
    have : (∑' k, hmain k)
        = (2 / t ^ 3) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]; ring
  -- connect `Σ hrem` to the Riemann sum of `Gw`: `Σ (guarded Gw(tk)) = t · Σ hrem`
  have hGwsum_eq : (∑' k : ℕ, if k = 0 then (0:ℝ) else Gw (t * (k : ℝ)))
      = t * ∑' k, hrem k := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Gw]
      ring
  -- the Riemann bound, transported
  have hRie := riemann_Gw_bound t ht ht1
  rw [hGwsum_eq] at hRie
  -- `|t·Σhrem − 1/(2t)| ≤ K`, and `t·Σhrem − 1/(2t) = t·(Σhrem − 1/(2t²))`
  set K : ℝ := (∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32 with hKdef
  have hfactor : t * (∑' k, hrem k) - (1 / t) * (1 / 2)
      = t * ((∑' k, hrem k) - 1 / (2 * t ^ 2)) := by
    have htne : t ≠ 0 := ht.ne'
    field_simp
  rw [hfactor, abs_mul, abs_of_pos ht] at hRie
  have hrem_bound : |(∑' k, hrem k) - 1 / (2 * t ^ 2)| ≤ K / t := by
    rw [le_div_iff₀ ht, mul_comm]
    exact hRie
  -- assemble
  rw [hM1_eq, hmain_eq]
  have harr : (2 * (Real.pi ^ 2 / 6) / t ^ 3 - ∑' k, hrem k)
      - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))
      = -((∑' k, hrem k) - 1 / (2 * t ^ 2)) := by ring
  rw [harr, abs_neg]
  exact hrem_bound
