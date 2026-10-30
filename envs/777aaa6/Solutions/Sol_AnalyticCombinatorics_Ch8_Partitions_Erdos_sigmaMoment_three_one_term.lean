-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_three_one_term
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:45.5085+00:00
-- url     : https://prove2.me/submissions/920abe05-64b2-401c-be0e-751587a8697a

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
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

/--
**The `M₂` Lambert identity** (termwise differentiation of the `M₁` identity):

  `Σ_m m²·σ(m)e^{−tm} = Σ_k k²·boseKernel3(tk)`.
-/
theorem sigmaMoment_two_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 2 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ)) := by
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
    if m = 0 then (0:ℝ) else (m : ℝ) * Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ)
    else -((m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
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
      have := hexp.const_mul ((m : ℝ) * Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s,
      ‖fσ' m u‖ ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m := by
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
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 2 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rwa [habs] at this
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
      have hs1 : (m : ℝ) * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
          ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum (by positivity)
      have hs2 : (m : ℝ) * Sigma.sigmaR m * r ^ m
          ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m := by
        have hmn : (0:ℝ) ≤ (m : ℝ) := by linarith
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hmn) hσn) (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else (k : ℝ) * boseKernel2 (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel3 (u * (k : ℝ))) * (k : ℝ) ^ 2) with hgB'def
  set CB := (6:ℝ) / (1 - Real.exp (-(t / 2))) ^ 4 with hCBdef
  have het2 : Real.exp (-(t / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hdt2 : 0 < 1 - Real.exp (-(t / 2)) := by linarith
  have hCB0 : 0 < CB := by
    rw [hCBdef]
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
      have houter := boseKernel2_hasDerivAt hukpos
      have hcomp := houter.comp u hinner
      have := hcomp.const_mul ((k : ℝ))
      convert this using 1
      ring
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) ^ 2 * CB * r ^ k := by
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
      have hbk3_nonneg := boseKernel3_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk3_nonneg, abs_pow,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel3_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel3 (u * (k : ℝ)) * (k : ℝ) ^ 2
          ≤ (6 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (6 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) * (k : ℝ) ^ 2
          = (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k
          = (k : ℝ) ^ 2 * CB * r ^ k := by
        rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
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
      have hbk2_nonneg := boseKernel2_nonneg htkpos
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hbk2_nonneg, Nat.abs_cast]
      have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
      have hle := boseKernel2_le ht2 hzge
      have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      -- k·boseKernel2(tk) ≤ k·(2e^{−tk}/(1−e^{−t/2})³) ≤ k²·CB·r^k
      have hstep1 : (k : ℝ) * boseKernel2 (t * (k : ℝ))
          ≤ (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have hstep2 : (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3)
          ≤ (k : ℝ) ^ 2 * CB * r ^ k := by
        rw [hCBdef]
        have hcoef : 2 / (1 - Real.exp (-(t / 2))) ^ 3
            ≤ 6 / (1 - Real.exp (-(t / 2))) ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hd1 : 1 - Real.exp (-(t / 2)) ≤ 1 := by
            have := Real.exp_pos (-(t / 2))
            linarith
          have hp3 : (0:ℝ) < (1 - Real.exp (-(t / 2))) ^ 3 := by positivity
          nlinarith [hp3, hd1, hdt2]
        have hexp0 := Real.exp_pos (-(t * (k : ℝ)))
        have hr_pow : (0:ℝ) < r ^ k := pow_pos hr0 k
        have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        calc (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3)
            = (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(t * (k : ℝ))) := by
              ring
          _ ≤ (k : ℝ) * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(t * (k : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hexp0.le
              exact mul_le_mul_of_nonneg_left hcoef (by linarith)
          _ ≤ (k : ℝ) * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ ≤ (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k := by
              apply mul_le_mul_of_nonneg_right _ hr_pow.le
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
      exact le_trans hstep1 hstep2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_one_lambert (t := u) hu0
    have hLHS : sigmaMoment 1 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
      refine tsum_congr fun m => ?_
      by_cases hm : m = 0
      · subst hm
        simp [hfσdef]
      · simp only [hfσdef, if_neg hm]
        rw [pow_one]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (u * (k : ℝ)))
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
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 2 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ))) := by
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
# The order-4 Bose kernel `boseKernel4 = ∑_d d⁴ e^{−dz}`

Closed form via Eulerian numbers `⟨4,k⟩ = 1, 11, 11, 1`:

  `boseKernel4 z = e^{−z}(1 + 11e^{−z} + 11e^{−2z} + e^{−3z}) / (1 − e^{−z})⁵ ~ 24/z⁵`.

`boseKernel3` has derivative `−boseKernel4` on `(0,∞)` (the differentiation step that yields the
`M₃` Lambert identity from the `M₂` one).  Opus-authored.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_d d⁴ e^{−dz}` in closed form (Eulerian numbers `1,11,11,1`). -/
noncomputable def boseKernel4 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + 11 * Real.exp (-z) + 11 * Real.exp (-z) ^ 2 + Real.exp (-z) ^ 3)
    / (1 - Real.exp (-z)) ^ 5

/-- `boseKernel3` has derivative `−boseKernel4` on `(0,∞)` (quotient rule). -/
lemma boseKernel3_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel3 (-boseKernel4 z) z := by
  have hy1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hd0 : (0 : ℝ) < 1 - Real.exp (-z) := by linarith
  have hy : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-z)) z := by
    have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa using (Real.hasDerivAt_exp (-z)).comp z hinner
  -- numerator  N(u) = e^{−u}·(1 + 4 e^{−u} + (e^{−u})²)  (matching boseKernel3's parenthesization)
  have hone := ((hy.const_mul (4 : ℝ)).const_add (1 : ℝ)).add (hy.pow 2)
  have hN := hy.mul hone
  -- denominator  D(u) = (1 − e^{−u})⁴
  have hbase : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-z)) z := by
    simpa using hy.const_sub 1
  have hD := hbase.pow 4
  have hQ := hN.div hD (pow_ne_zero 4 hd0.ne')
  have hshape : boseKernel3
      = fun u : ℝ => Real.exp (-u) * (1 + 4 * Real.exp (-u) + Real.exp (-u) ^ 2)
          / (1 - Real.exp (-u)) ^ 4 := rfl
  rw [hshape]
  convert hQ using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply]
  rw [boseKernel4]
  field_simp
  ring

/-- `boseKernel4 ≥ 0` on `(0,∞)`. -/
lemma boseKernel4_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel4 z := by
  have h1 : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel4]
  positivity

/-- Tail comparison: `boseKernel4(z) ≤ 24 e^{−z}/(1−e^{−a})⁵` for `z ≥ a > 0`. -/
lemma boseKernel4_le {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) :
    boseKernel4 z ≤ 24 * Real.exp (-z) / (1 - Real.exp (-a)) ^ 5 := by
  have hea : Real.exp (-a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hda : 0 < 1 - Real.exp (-a) := by linarith
  have hez : Real.exp (-z) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  have h1z : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hdz : 0 < 1 - Real.exp (-z) := by linarith
  have hd_mono : 1 - Real.exp (-a) ≤ 1 - Real.exp (-z) := by linarith
  rw [boseKernel4]
  apply div_le_div₀ (by positivity)
  · have h2 : 1 + 11 * Real.exp (-z) + 11 * Real.exp (-z) ^ 2 + Real.exp (-z) ^ 3 ≤ 24 := by
      nlinarith [Real.exp_pos (-z), hez, hea, h1z]
    nlinarith [Real.exp_pos (-z)]
  · positivity
  · exact pow_le_pow_left₀ hda.le hd_mono 5

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# The `M₃` Lambert identity

Termwise differentiation of the `M₂` identity (`sigmaMoment_two_lambert`) gives

  `Σ_m m³·σ(m)e^{−tm} = Σ_k k³·boseKernel4(tk)`,

using `boseKernel3_hasDerivAt : HasDerivAt boseKernel3 (−boseKernel4) z`.
Faithful mirror of `sigmaMoment_two_lambert`, powers shifted `+1`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Set
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **The `M₃` Lambert identity.** -/
theorem sigmaMoment_three_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 3 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ)) := by
  classical
  have ht2 : 0 < t / 2 := by linarith
  set s := Set.Ioi (t / 2) with hsdef
  have hs_open : IsOpen s := isOpen_Ioi
  have hs_conn : IsPreconnected s := (convex_Ioi _).isPreconnected
  have hts : t ∈ s := by
    rw [hsdef]; exact Set.mem_Ioi.mpr (by linarith)
  set r := Real.exp (-(t / 2)) with hrdef
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  have hr0 : 0 < r := Real.exp_pos _
  -- ===== σ-side: differentiate  m²·σ·e^{−um}  →  −m³·σ·e^{−um} =====
  set fσ := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ)
    else -((m : ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
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
      have := hexp.const_mul ((m : ℝ) ^ 2 * Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s,
      ‖fσ' m u‖ ≤ (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m := by
    intro m u hu
    by_cases hm : m = 0
    · subst hm; simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
        have := sigmaR_nonneg m; positivity)]
      have hum : Real.exp (-u * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hu2 : t / 2 < u := hu
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
        nlinarith
      have := sigmaR_nonneg m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      exact mul_le_mul_of_nonneg_left hum (by positivity)
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 3 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rwa [habs] at this
  have hσ_at_t : Summable (fun m : ℕ => fσ m t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) hσ_u_summable
    by_cases hm : m = 0
    · subst hm; simp [hfσdef]
    · simp only [hfσdef, if_neg hm]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := sigmaR_nonneg m; positivity)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hum : Real.exp (-t * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hσn := sigmaR_nonneg m
      have hs1 : (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
          ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum (by positivity)
      have hs2 : (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m
          ≤ (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m := by
        have hmn : (0:ℝ) ≤ (m : ℝ) := by linarith
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) (by positivity : (0:ℝ) ≤ (m:ℝ)^2)) hσn)
          (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side: differentiate  k²·boseKernel3(uk)  →  −k³·boseKernel4(uk) =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else (k : ℝ) ^ 2 * boseKernel3 (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel4 (u * (k : ℝ))) * (k : ℝ) ^ 3) with hgB'def
  set CB := (24:ℝ) / (1 - Real.exp (-(t / 2))) ^ 5 with hCBdef
  have het2 : Real.exp (-(t / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hdt2 : 0 < 1 - Real.exp (-(t / 2)) := by linarith
  have hCB0 : 0 < CB := by rw [hCBdef]; positivity
  have hB_deriv : ∀ k : ℕ, ∀ u ∈ s, HasDerivAt (gB k) (gB' k u) u := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp only [hgBdef, hgB'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hgBdef, hgB'def, if_neg hk]
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hu0 : 0 < u := lt_trans ht2 hu
      have hukpos : 0 < u * (k : ℝ) := by positivity
      have hinner : HasDerivAt (fun u : ℝ => u * (k : ℝ)) ((k : ℝ)) u := by
        simpa using (hasDerivAt_id u).mul_const ((k : ℝ))
      have houter := boseKernel3_hasDerivAt hukpos
      have hcomp := houter.comp u hinner
      have := (hcomp.const_mul ((k : ℝ) ^ 2))
      convert this using 1
      ring
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) ^ 3 * CB * r ^ k := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk; simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hu2 : t / 2 < u := hu
      have hu0 : 0 < u := lt_trans ht2 hu2
      have hukpos : 0 < u * (k : ℝ) := mul_pos hu0 (by linarith)
      have hbk4_nonneg := boseKernel4_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk4_nonneg, abs_pow,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel4_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel4 (u * (k : ℝ)) * (k : ℝ) ^ 3
          ≤ (24 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 5) * (k : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (24 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 5) * (k : ℝ) ^ 3
          = (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k
          = (k : ℝ) ^ 3 * CB * r ^ k := by rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) ^ 3 * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) ^ 3 * r ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have := hbase.mul_left CB
    refine this.congr fun k => ?_
    ring
  have hB_at_t : Summable (fun k : ℕ => gB k t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hB_u_summable.congr (fun k => rfl))
    by_cases hk : k = 0
    · subst hk; simp [hgBdef]
    · simp only [hgBdef, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hbk3_nonneg := boseKernel3_nonneg htkpos
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hbk3_nonneg, abs_pow, Nat.abs_cast]
      have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
      have hle := boseKernel3_le ht2 hzge
      have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      -- k²·boseKernel3(tk) ≤ k²·(6 e^{−tk}/(1−e^{−t/2})⁴) ≤ k³·CB·r^k
      have hstep1 : (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ))
          ≤ (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have hstep2 : (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4)
          ≤ (k : ℝ) ^ 3 * CB * r ^ k := by
        rw [hCBdef]
        have hcoef : 6 / (1 - Real.exp (-(t / 2))) ^ 4
            ≤ 24 / (1 - Real.exp (-(t / 2))) ^ 5 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hd1 : 1 - Real.exp (-(t / 2)) ≤ 1 := by
            have := Real.exp_pos (-(t / 2)); linarith
          have hp4 : (0:ℝ) < (1 - Real.exp (-(t / 2))) ^ 4 := by positivity
          nlinarith [hp4, hd1, hdt2]
        have hexp0 := Real.exp_pos (-(t * (k : ℝ)))
        have hr_pow : (0:ℝ) < r ^ k := pow_pos hr0 k
        have hk3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
        calc (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4)
            = (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(t * (k : ℝ))) := by
              ring
          _ ≤ (k : ℝ) ^ 2 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(t * (k : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hexp0.le
              exact mul_le_mul_of_nonneg_left hcoef (by positivity)
          _ ≤ (k : ℝ) ^ 2 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ ≤ (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k := by
              apply mul_le_mul_of_nonneg_right _ hr_pow.le
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact hk3
      exact le_trans hstep1 hstep2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_two_lambert (t := u) hu0
    have hLHS : sigmaMoment 2 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (u * (k : ℝ)))
        = ∑' k : ℕ, gB k u := by
      refine tsum_congr fun k => ?_
      by_cases hk : k = 0
      · subst hk; simp [hgBdef]
      · simp only [hgBdef, if_neg hk]
    rw [← hLHS, hML, ← hRHS]
  -- transfer the derivative + uniqueness
  have hA' : HasDerivAt (fun z => ∑' k : ℕ, gB k z) (∑' m : ℕ, fσ' m t) t :=
    hA.congr_of_eventuallyEq hEq.symm
  have huniq := hA'.unique hB
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 3 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm; simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ))) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      ring
  rw [hLHS', hRHS'] at huniq
  linarith [huniq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Near-zero certificate for `reg4 = boseKernel4 − 24/z⁵`

`|boseKernel4 z − 24/z⁵| ≤ 2645` on `(0,1]`, via the degree-10 cancellation certificate
(`y = e^z − 1`, `boseKernel4 = (24+60y+50y²+15y³+y⁴)/y⁵`, Taylor `P5` of order 5).
Mirror of `MassRateReg3`, one order higher.  Opus-authored (sympy-generated polynomials).
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Taylor remainder: `|e^z − 1 − (z + z²/2 + z³/6 + z⁴/24 + z⁵/120)| ≤ z⁶` on `[0,1]`. -/
lemma exp_sub_one_order5_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6 - x ^ 4 / 24 - x ^ 5 / 120| ≤ x ^ 6 := by
  have habs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.exp_bound habs (n := 6) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 6, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs6 : |x| ^ 6 = x ^ 6 := by rw [abs_of_nonneg hx0]
  rw [habs6] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6 - x ^ 4 / 24 - x ^ 5 / 120|
      = |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| := by ring_nf
    _ ≤ x ^ 6 * ((6 : ℕ).succ / ((Nat.factorial 6 : ℝ) * 6)) := h
    _ ≤ x ^ 6 := by
        have hx6 : (0 : ℝ) ≤ x ^ 6 := by positivity
        have hc : ((6 : ℕ).succ : ℝ) / ((Nat.factorial 6 : ℝ) * 6) ≤ 1 := by norm_num [Nat.factorial]
        nlinarith [hx6, hc]

lemma reg4_Q0_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15| ≤ (2 : ℝ) := by
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
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15]⟩

lemma reg4_Q1_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16| ≤ (658 : ℝ) := by
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
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16]⟩

lemma reg4_Q2_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12| ≤ (1070 : ℝ) := by
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
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12]⟩

lemma reg4_Q3_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8| ≤ (686 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8]⟩

lemma reg4_Q4_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3| ≤ (205 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hn1, hn2, hn3], by linarith [hp1, hp2, hp3, hn1, hn2, hn3]⟩

lemma reg4_Q5_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-24 : ℝ)| ≤ (24 : ℝ) := by

  rw [abs_le]
  refine ⟨by linarith [], by linarith []⟩

/-- The degree-10 cancellation identity (`δ = y − P5`).  Pure `ring`. -/
lemma reg4_split_identity (z y : ℝ) :
    z ^ 5 * (24 + 60 * y + 50 * y ^ 2 + 15 * y ^ 3 + y ^ 4) - 24 * y ^ 5
      = z ^ 10 * ((1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) * z ^ 4 * ((-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 2 * z ^ 3 * ((-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 3 * z ^ 2 * ((-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 4 * z * ((-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 5 * ((-24 : ℝ)) := by
  ring

/-- Closed form of `boseKernel4` in `y = e^z − 1`. -/
lemma boseKernel4_yform {z : ℝ} (hz : 0 < z) :
    boseKernel4 z
      = (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
          + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) / (Real.exp z - 1) ^ 5 := by
  have he0 : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  have he1 : (1 : ℝ) < Real.exp z := by nlinarith [Real.add_one_le_exp z, hz]
  have hy0 : Real.exp z - 1 ≠ 0 := by linarith
  have hinv1 : (Real.exp z)⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one (Real.exp_pos z)]; exact he1
  have hq1 : (1 : ℝ) - (Real.exp z)⁻¹ ≠ 0 := by linarith
  rw [boseKernel4, Real.exp_neg]
  field_simp
  ring

/-- Numerator bound: `|reg4Num(z, e^z−1)| ≤ 2645 z¹⁰` on `(0,1]`. -/
lemma reg4_num_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |z ^ 5 * (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
        + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) - 24 * (Real.exp z - 1) ^ 5|
      ≤ 2645 * z ^ 10 := by
  set y : ℝ := Real.exp z - 1 with hydef
  have hz10nn : (0:ℝ) ≤ z ^ 10 := by positivity
  set δ : ℝ := y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120) with hδdef
  have hδbd : |δ| ≤ z ^ 6 := by
    rw [hδdef, hydef]
    have h := exp_sub_one_order5_bound hz0.le hz1
    convert h using 2
    ring
  have hδ2 : δ ^ 2 ≤ z ^ 12 := by
    have h1 : |δ| ^ 2 ≤ (z ^ 6) ^ 2 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 2
    have h3 : δ ^ 2 = |δ| ^ 2 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; calc |δ| ^ 2 ≤ (z ^ 6) ^ 2 := h1
      _ = z ^ 12 := by ring
  have hδ3 : |δ| ^ 3 ≤ z ^ 18 := by
    calc |δ| ^ 3 ≤ (z ^ 6) ^ 3 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 3
      _ = z ^ 18 := by ring
  have hδ4 : δ ^ 4 ≤ z ^ 24 := by
    have h1 : |δ| ^ 4 ≤ (z ^ 6) ^ 4 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 4
    have h3 : δ ^ 4 = |δ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; calc |δ| ^ 4 ≤ (z ^ 6) ^ 4 := h1
      _ = z ^ 24 := by ring
  have hδ5 : |δ| ^ 5 ≤ z ^ 30 := by
    calc |δ| ^ 5 ≤ (z ^ 6) ^ 5 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 5
      _ = z ^ 30 := by ring
  have r15 : z ^ 15 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r20 : z ^ 20 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r25 : z ^ 25 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r30 : z ^ 30 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  rw [reg4_split_identity z y, ← hδdef]
  set Q0 := (1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15 with hQ0def
  set Q1 := (-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16 with hQ1def
  set Q2 := (-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12 with hQ2def
  set Q3 := (-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8 with hQ3def
  set Q4 := (-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3 with hQ4def
  set Q5 := (-24 : ℝ) with hQ5def
  have hQ0 := reg4_Q0_bound hz0.le hz1
  have hQ1 := reg4_Q1_bound hz0.le hz1
  have hQ2 := reg4_Q2_bound hz0.le hz1
  have hQ3 := reg4_Q3_bound hz0.le hz1
  have hQ4 := reg4_Q4_bound hz0.le hz1
  have hQ5 := reg4_Q5_bound hz0.le hz1
  have e0 : |z ^ 10 * Q0| ≤ z ^ 10 * 2 := by
    rw [abs_mul, abs_of_nonneg hz10nn]; exact mul_le_mul_of_nonneg_left hQ0 hz10nn
  have e1 : |δ * z ^ 4 * Q1| ≤ z ^ 10 * 658 := by
    rw [show δ * z ^ 4 * Q1 = δ * (z ^ 4 * Q1) by ring, abs_mul]
    have hb : |z ^ 4 * Q1| ≤ z ^ 4 * 658 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 4)]
      exact mul_le_mul_of_nonneg_left hQ1 (by positivity)
    calc |δ| * |z ^ 4 * Q1| ≤ z ^ 6 * (z ^ 4 * 658) := mul_le_mul hδbd hb (abs_nonneg _) (by positivity)
      _ = z ^ 10 * 658 := by ring
  have e2 : |δ ^ 2 * z ^ 3 * Q2| ≤ z ^ 10 * 1070 := by
    rw [show δ ^ 2 * z ^ 3 * Q2 = δ ^ 2 * (z ^ 3 * Q2) by ring, abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have hb : |z ^ 3 * Q2| ≤ z ^ 3 * 1070 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 3)]
      exact mul_le_mul_of_nonneg_left hQ2 (by positivity)
    calc δ ^ 2 * |z ^ 3 * Q2| ≤ z ^ 12 * (z ^ 3 * 1070) := mul_le_mul hδ2 hb (abs_nonneg _) (by positivity)
      _ = z ^ 15 * 1070 := by ring
      _ ≤ z ^ 10 * 1070 := mul_le_mul_of_nonneg_right r15 (by norm_num)
  have e3 : |δ ^ 3 * z ^ 2 * Q3| ≤ z ^ 10 * 686 := by
    rw [show δ ^ 3 * z ^ 2 * Q3 = δ ^ 3 * (z ^ 2 * Q3) by ring, abs_mul,
      show |δ ^ 3| = |δ| ^ 3 from by rw [abs_pow]]
    have hb : |z ^ 2 * Q3| ≤ z ^ 2 * 686 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 2)]
      exact mul_le_mul_of_nonneg_left hQ3 (by positivity)
    calc |δ| ^ 3 * |z ^ 2 * Q3| ≤ z ^ 18 * (z ^ 2 * 686) := mul_le_mul hδ3 hb (abs_nonneg _) (by positivity)
      _ = z ^ 20 * 686 := by ring
      _ ≤ z ^ 10 * 686 := mul_le_mul_of_nonneg_right r20 (by norm_num)
  have e4 : |δ ^ 4 * z * Q4| ≤ z ^ 10 * 205 := by
    rw [show δ ^ 4 * z * Q4 = δ ^ 4 * (z * Q4) by ring, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ δ ^ 4)]
    have hb : |z * Q4| ≤ z * 205 := by
      rw [abs_mul, abs_of_nonneg hz0.le]
      exact mul_le_mul_of_nonneg_left hQ4 hz0.le
    calc δ ^ 4 * |z * Q4| ≤ z ^ 24 * (z * 205) := mul_le_mul hδ4 hb (abs_nonneg _) (by positivity)
      _ = z ^ 25 * 205 := by ring
      _ ≤ z ^ 10 * 205 := mul_le_mul_of_nonneg_right r25 (by norm_num)
  have e5 : |δ ^ 5 * Q5| ≤ z ^ 10 * 24 := by
    rw [abs_mul, show |δ ^ 5| = |δ| ^ 5 from by rw [abs_pow]]
    have hb : |Q5| ≤ 24 := by rw [hQ5def, abs_of_nonpos (by norm_num)]; norm_num
    calc |δ| ^ 5 * |Q5| ≤ z ^ 30 * 24 := mul_le_mul hδ5 hb (abs_nonneg _) (by positivity)
      _ ≤ z ^ 10 * 24 := mul_le_mul_of_nonneg_right r30 (by norm_num)
  have hassoc : z ^ 10 * Q0 + δ * z ^ 4 * Q1 + δ ^ 2 * z ^ 3 * Q2 + δ ^ 3 * z ^ 2 * Q3
        + δ ^ 4 * z * Q4 + δ ^ 5 * Q5
      = z ^ 10 * Q0 + (δ * z ^ 4 * Q1 + (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3
        + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)))) := by ring
  rw [hassoc]
  have t1 := abs_add_le (z ^ 10 * Q0) (δ * z ^ 4 * Q1 + (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5))))
  have t2 := abs_add_le (δ * z ^ 4 * Q1) (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)))
  have t3 := abs_add_le (δ ^ 2 * z ^ 3 * Q2) (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5))
  have t4 := abs_add_le (δ ^ 3 * z ^ 2 * Q3) (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)
  have t5 := abs_add_le (δ ^ 4 * z * Q4) (δ ^ 5 * Q5)
  linarith [t1, t2, t3, t4, t5, e0, e1, e2, e3, e4, e5]

/-- **Near-zero bound** `|boseKernel4 z − 24/z⁵| ≤ 2645` on `(0,1]`. -/
lemma reg4_bdd_near_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |boseKernel4 z - 24 / z ^ 5| ≤ 2645 := by
  have hyz : z ≤ Real.exp z - 1 := by linarith [Real.add_one_le_exp z]
  have hypos : 0 < Real.exp z - 1 := by linarith
  have hy0 : Real.exp z - 1 ≠ 0 := hypos.ne'
  have hz0' : z ≠ 0 := hz0.ne'
  have heq : boseKernel4 z - 24 / z ^ 5
      = (z ^ 5 * (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
          + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) - 24 * (Real.exp z - 1) ^ 5)
        / (z ^ 5 * (Real.exp z - 1) ^ 5) := by
    rw [boseKernel4_yform hz0]
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos (by positivity) (pow_pos hypos 5))]
  rw [div_le_iff₀ (mul_pos (by positivity) (pow_pos hypos 5))]
  have hnum := reg4_num_le hz0 hz1
  have hden : z ^ 10 ≤ z ^ 5 * (Real.exp z - 1) ^ 5 := by
    have h5 : z ^ 5 ≤ (Real.exp z - 1) ^ 5 := pow_le_pow_left₀ hz0.le hyz 5
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ z ^ 5)]
  have hscaled := mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ) ≤ 2645)
  linarith [hnum, hscaled]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: `M₃` one-term asymptotics

`|M₃(t) − 24(π²/6)/t⁵| ≤ K/t⁴` on `0 < t ≤ 1`.  Split `M₃ = Σ'_{k} k³·boseKernel4(tk)` via
`boseKernel4 z = 24/z⁵ + reg4(z)`: singular part sums (Basel) to `24(π²/6)/t⁵`, remainder
`Σ'_k k³·reg4(tk)` bounded by the weighted-decay keystone (`j=3`, `Cf=2645`, `Df=24`).
Mirror of `MassRateMomentTwoAsymp`, powers shifted +1.  Opus-authored.
-/

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `reg4` tail bound: `|boseKernel4 z − 24/z⁵| ≤ (24/(1−e^{−1})⁵)·e^{−z/2} + 24/z⁵` for `z > 1`. -/
lemma reg4_tail {z : ℝ} (hz1 : 1 < z) :
    |boseKernel4 z - 24 / z ^ 5|
      ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) + 24 / z ^ 5 := by
  have hzpos : 0 < z := by linarith
  have hb4nn : 0 ≤ boseKernel4 z := boseKernel4_nonneg hzpos
  have hle := boseKernel4_le (by norm_num : (0:ℝ) < 1) hz1.le
  have hexp_le : Real.exp (-z) ≤ Real.exp (-z / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have htri : |boseKernel4 z - 24 / z ^ 5| ≤ |boseKernel4 z| + |24 / z ^ 5| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  rw [abs_of_nonneg hb4nn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 24 / z ^ 5)] at htri
  have hDpos : (0:ℝ) < (1 - Real.exp (-1)) ^ 5 := by
    have he : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have hb : (0:ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  have hstep : boseKernel4 z ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) := by
    refine hle.trans ?_
    rw [show 24 * Real.exp (-z) / (1 - Real.exp (-1)) ^ 5
        = (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z) from by ring]
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  linarith [htri, hstep]

/-- Global `reg4` bound: `|reg4 z| ≤ B₄·e^{−z/2} + 2645/z⁵` for all `z > 0`. -/
lemma reg4_global_bound {z : ℝ} (hz : 0 < z) :
    |boseKernel4 z - 24 / z ^ 5|
      ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) + 2645 / z ^ 5 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := reg4_bdd_near_zero hz hz1
    have h2 : (2645:ℝ) ≤ 2645 / z ^ 5 := by
      rw [le_div_iff₀ (by positivity)]
      have : z ^ 5 ≤ 1 := pow_le_one₀ hz.le hz1
      nlinarith
    have he' : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have hden_pos : 0 < 1 - Real.exp (-1) := by linarith
    have h3 : (0:ℝ) ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) := by positivity
    linarith
  · have h1 := reg4_tail hz1
    have h2 : (24:ℝ) / z ^ 5 ≤ 2645 / z ^ 5 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-- Summability of `k³·|reg4(tk)|`. -/
lemma summable_weighted_absReg4 {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => if k = 0 then (0:ℝ)
      else (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5|) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set B₄ : ℝ := 24 / (1 - Real.exp (-1)) ^ 5 with hB4
  have hdom : Summable (fun k : ℕ =>
      (k : ℝ) ^ 3 * (B₄ * Real.exp (-t / 2) ^ k) + 2645 / t ^ 5 * (1 / ((k : ℝ)) ^ 2)) := by
    apply Summable.add
    · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left B₄
      refine this.congr fun k => ?_
      ring
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
      have hg := reg4_global_bound htkpos
      have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have htne : t ≠ 0 := ht.ne'
      have hpoly : (k : ℝ) ^ 3 * (2645 / (t * (k : ℝ)) ^ 5) = 2645 / t ^ 5 * (1 / (k : ℝ) ^ 2) := by
        rw [mul_pow, show (k : ℝ) ^ 5 = (k : ℝ) ^ 3 * (k : ℝ) ^ 2 from by ring]
        field_simp
      calc (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5|
          ≤ (k : ℝ) ^ 3 * (B₄ * Real.exp (-(t * (k : ℝ)) / 2) + 2645 / (t * (k : ℝ)) ^ 5) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hB4]; exact hg
        _ = (k : ℝ) ^ 3 * (B₄ * Real.exp (-t / 2) ^ k) + 2645 / t ^ 5 * (1 / (k : ℝ) ^ 2) := by
            rw [mul_add, hexp_eq, hpoly]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter
open scoped Topology
set_option maxHeartbeats 1000000
theorem solution {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 3 t - 24 * (Real.pi ^ 2 / 6) / t ^ 5|
      ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
          / t ^ 4 := by
  classical
  have hML := sigmaMoment_three_lambert ht0
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) ^ 3 * (boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (24 / t ^ 5) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absReg4 ht0
    refine habs.congr fun k => ?_
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
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
    have := hb.mul_left (24 / t ^ 5)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  -- per-term: lambert summand = hmain + hrem
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ)))
        = hmain k + hrem k := by
    intro k
    simp only [hmaindef, hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htne : t ≠ 0 := ht0.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
      ring
  have hM3_eq : sigmaMoment 3 t = (∑' k, hmain k) + (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_add hrem_summ]
  have hmain_eq : (∑' k, hmain k) = 24 * (Real.pi ^ 2 / 6) / t ^ 5 := by
    have : (∑' k, hmain k)
        = (24 / t ^ 5) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]
    ring
  have hrem_abs_bound : |∑' k, hrem k|
      ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
          / t ^ 4 := by
    have hnorm : |∑' k, hrem k| ≤ ∑' k, |hrem k| := by
      have hns : Summable (fun k => ‖hrem k‖) := by
        have := summable_weighted_absReg4 ht0
        refine this.congr fun k => ?_
        simp only [hremdef]
        by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
      have h1 := norm_tsum_le_tsum_norm hns
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
    refine le_trans hnorm ?_
    have habs_eq : (∑' k, |hrem k|)
        = ∑' k : ℕ, if k = 0 then (0:ℝ)
            else (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5| := by
      apply tsum_congr; intro k
      simp only [hremdef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk, abs_mul, abs_pow, Nat.abs_cast]
    rw [habs_eq]
    exact weighted_decay_sum_bound 3 (fun z => boseKernel4 z - 24 / z ^ 5)
      2645 (24 / (1 - Real.exp (-1)) ^ 5) 24
      (by norm_num) (by
          have he' : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
          have hden_pos : 0 < 1 - Real.exp (-1) := by linarith
          positivity) (by norm_num)
      (fun z hz0 hz1 => reg4_bdd_near_zero hz0 hz1)
      (fun z hz1 => reg4_tail hz1)
      ht0 ht1
  rw [hM3_eq, hmain_eq]
  have harr : (24 * (Real.pi ^ 2 / 6) / t ^ 5 + ∑' k, hrem k) - 24 * (Real.pi ^ 2 / 6) / t ^ 5
      = ∑' k, hrem k := by ring
  rw [harr]
  exact hrem_abs_bound
