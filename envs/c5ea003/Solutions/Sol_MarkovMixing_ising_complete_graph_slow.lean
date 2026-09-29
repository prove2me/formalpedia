-- Prove2me | solution 1 for MarkovMixing.ising_complete_graph_slow
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T04:43:38.871795+00:00
-- url     : https://prove2.me/submissions/9f778336-fcdd-48f9-b3aa-2d7fb34f10b1

import Definitions.Def_mm_ising
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_glauber_stationary
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Slow mixing of the Curie–Weiss Glauber dynamics (LPW Theorem 15.3(ii))
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Bottleneck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `π` conditioned on `S`. -/
private def condDist (π : V → ℝ) (S : Finset V) : V → ℝ :=
  fun x => if x ∈ S then π x / (∑ y ∈ S, π y) else 0

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma condDist_le (π : V → ℝ) (hpos : ∀ x, 0 < π x) (S : Finset V)
    (hS : S.Nonempty) (x : V) : condDist π S x ≤ π x / (∑ y ∈ S, π y) := by
  have hZ : 0 < ∑ y ∈ S, π y := Finset.sum_pos (fun y _ => hpos y) hS
  rw [condDist]
  split_ifs with h
  · exact le_refl _
  · exact le_of_lt (div_pos (hpos x) hZ)

private lemma condDist_nonneg (π : V → ℝ) (hpos : ∀ x, 0 < π x) (S : Finset V)
    (hS : S.Nonempty) (x : V) : 0 ≤ condDist π S x := by
  have hZ : 0 < ∑ y ∈ S, π y := Finset.sum_pos (fun y _ => hpos y) hS
  rw [condDist]
  split_ifs
  · exact le_of_lt (div_pos (hpos x) hZ)
  · exact le_refl 0

private lemma condDist_sum (π : V → ℝ) (hpos : ∀ x, 0 < π x) (S : Finset V)
    (hS : S.Nonempty) : ∑ x, condDist π S x = 1 := by
  have hZ : 0 < ∑ y ∈ S, π y := Finset.sum_pos (fun y _ => hpos y) hS
  simp only [condDist]
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun x : V => x ∈ S) = S := by ext x; simp
  rw [hfil, ← sum_div_const, div_self (ne_of_gt hZ)]

/-- The distribution of the chain started from `π` conditioned on `S`. -/
private def evolved (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) (t : ℕ) : V → ℝ :=
  Matrix.vecMul (condDist π S) (P ^ t)

private lemma evolved_zero (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) :
    evolved P π S 0 = condDist π S := by
  rw [evolved, pow_zero, Matrix.vecMul_one]

private lemma evolved_succ (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) (t : ℕ) (x : V) :
    evolved P π S (t + 1) x = ∑ y, evolved P π S t y * P y x := by
  rw [evolved, evolved, pow_succ, ← Matrix.vecMul_vecMul]
  rfl

private lemma evolved_nonneg (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (hS : S.Nonempty) :
    ∀ (t : ℕ) (x : V), 0 ≤ evolved P π S t x := by
  intro t
  induction t with
  | zero => intro x; rw [evolved_zero]; exact condDist_nonneg π hpos S hS x
  | succ t ih =>
      intro x
      rw [evolved_succ]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (ih y) (hP.1 y x)

private lemma evolved_sum (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (hS : S.Nonempty) :
    ∀ t : ℕ, ∑ x, evolved P π S t x = 1 := by
  intro t
  induction t with
  | zero => rw [evolved_zero]; exact condDist_sum π hpos S hS
  | succ t ih =>
      rw [Finset.sum_congr rfl fun x _ => evolved_succ P π S t x, Finset.sum_comm]
      rw [Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm]
      rw [Finset.sum_congr rfl fun y _ => by rw [hP.2 y, mul_one]]
      exact ih

private lemma evolved_le (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hπ : IsStationary P π) (S : Finset V) (hS : S.Nonempty) :
    ∀ (t : ℕ) (x : V), evolved P π S t x ≤ π x / (∑ y ∈ S, π y) := by
  intro t
  induction t with
  | zero => intro x; rw [evolved_zero]; exact condDist_le π hpos S hS x
  | succ t ih =>
      intro x
      rw [evolved_succ]
      have hstep : ∑ y, evolved P π S t y * P y x
          ≤ ∑ y, (π y / (∑ z ∈ S, π z)) * P y x :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (ih y) (hP.1 y x)
      refine le_trans hstep ?_
      have hmul : ∑ y, (π y / (∑ z ∈ S, π z)) * P y x
          = (∑ y, π y * P y x) / (∑ z ∈ S, π z) := by
        rw [sum_div_const]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hmul]
      have hstat : ∑ y, π y * P y x = π x := by
        have := congrFun hπ.2 x
        simpa [Matrix.vecMul, dotProduct] using this
      rw [hstat]

private lemma evolved_escape (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hπ : IsStationary P π) (S : Finset V) (hS : S.Nonempty) :
    ∀ t : ℕ, ∑ x ∈ Sᶜ, evolved P π S t x ≤ (t : ℝ) * bottleneckRatio P π S := by
  have hZ : 0 < ∑ y ∈ S, π y := Finset.sum_pos (fun y _ => hpos y) hS
  have hphi : bottleneckRatio P π S
      = ∑ y ∈ S, (π y / (∑ z ∈ S, π z)) * (∑ x ∈ Sᶜ, P y x) := by
    rw [bottleneckRatio, sum_div_const]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, sum_div_const]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [edgeMeasure]
    ring
  intro t
  induction t with
  | zero =>
      rw [evolved_zero]
      have hz : ∀ x ∈ Sᶜ, condDist π S x = 0 := by
        intro x hx
        rw [condDist, if_neg (by simpa using hx)]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      simp
  | succ t ih =>
      have hexp : ∑ x ∈ Sᶜ, evolved P π S (t + 1) x
          = ∑ y, evolved P π S t y * (∑ x ∈ Sᶜ, P y x) := by
        rw [Finset.sum_congr rfl fun x _ => evolved_succ P π S t x, Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
      rw [hexp, ← Finset.sum_add_sum_compl S
        (fun y => evolved P π S t y * (∑ x ∈ Sᶜ, P y x))]
      have hA : ∑ y ∈ S, evolved P π S t y * (∑ x ∈ Sᶜ, P y x)
          ≤ bottleneckRatio P π S := by
        rw [hphi]
        refine Finset.sum_le_sum fun y _ => ?_
        refine mul_le_mul_of_nonneg_right
          (evolved_le P hP π hpos hπ S hS t y) ?_
        exact Finset.sum_nonneg fun x _ => hP.1 y x
      have hB : ∑ y ∈ Sᶜ, evolved P π S t y * (∑ x ∈ Sᶜ, P y x)
          ≤ ∑ y ∈ Sᶜ, evolved P π S t y := by
        refine Finset.sum_le_sum fun y _ => ?_
        refine mul_le_of_le_one_right (evolved_nonneg P hP π hpos S hS t y) ?_
        rw [← hP.2 y]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => hP.1 y x)
      have : (((t : ℝ) + 1)) * bottleneckRatio P π S
          = bottleneckRatio P π S + (t : ℝ) * bottleneckRatio P π S := by ring
      push_cast
      rw [this]
      linarith [hA, hB, ih]

private lemma tv_le_sup (μ ν : V → ℝ) (A : Finset V) :
    |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν := by
  rw [tvDist]
  refine le_ciSup (Set.Finite.bddAbove
    (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|).toFinite) A

private lemma tv_evolved_le (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (S : Finset V) (hS : S.Nonempty) (t : ℕ) :
    tvDist (evolved P π S t) π ≤ distStationary P π t := by
  have hc0 := condDist_nonneg π hpos S hS
  have hc1 := condDist_sum π hpos S hS
  rw [tvDist]
  refine ciSup_le fun A => ?_
  have hexp : ∑ x ∈ A, evolved P π S t x
      = ∑ y, condDist π S y * ∑ x ∈ A, (P ^ t) y x := by
    simp only [evolved, Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  have hpi : ∑ x ∈ A, π x = ∑ y, condDist π S y * ∑ x ∈ A, π x := by
    rw [← Finset.sum_mul, hc1, one_mul]
  rw [hexp, hpi, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y : V,
      |condDist π S y * (∑ x ∈ A, (P ^ t) y x) - condDist π S y * (∑ x ∈ A, π x)|
        ≤ condDist π S y * distStationary P π t := by
    intro y
    rw [← mul_sub, abs_mul, abs_of_nonneg (hc0 y)]
    refine mul_le_mul_of_nonneg_left ?_ (hc0 y)
    refine le_trans (tv_le_sup (rowDist P t y) π A) ?_
    rw [distStationary]
    refine le_ciSup (Set.Finite.bddAbove
      (Set.range fun z : V => tvDist (rowDist P t z) π).toFinite) y
  refine le_trans (Finset.sum_le_sum fun y _ => hterm y) ?_
  rw [← Finset.sum_mul, hc1, one_mul]

private lemma dist_ge_bottleneck (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hπ : IsStationary P π) (S : Finset V) (hS : S.Nonempty)
    (t : ℕ) :
    (∑ x ∈ Sᶜ, π x) - (t : ℝ) * bottleneckRatio P π S ≤ distStationary P π t := by
  refine le_trans ?_ (tv_evolved_le P hP π hpos S hS t)
  have h1 : (∑ x ∈ Sᶜ, π x) - ∑ x ∈ Sᶜ, evolved P π S t x
      ≤ tvDist (evolved P π S t) π := by
    refine le_trans ?_ (tv_le_sup (evolved P π S t) π Sᶜ)
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith [evolved_escape P hP π hpos hπ S hS t, h1]

private lemma bottleneck_tmix (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hπ : IsStationary P π) (S : Finset V) (hS : S.Nonempty)
    (hhalf : (2 : ℝ)⁻¹ ≤ ∑ x ∈ Sᶜ, π x)
    (hne : {t : ℕ | distStationary P π t ≤ 1 / 4}.Nonempty)
    (T : ℕ) (hT : (T : ℝ) * bottleneckRatio P π S < 1 / 4) :
    T ≤ tMix P π := by
  have hmem : distStationary P π (tMix P π) ≤ 1 / 4 := by
    have := Nat.sInf_mem hne
    simpa [tMix, mixingTime] using this
  by_contra hcon
  push_neg at hcon
  have hle := dist_ge_bottleneck P hP π hpos hπ S hS (tMix P π)
  have hmono : ((tMix P π : ℕ) : ℝ) * bottleneckRatio P π S
      ≤ (T : ℝ) * bottleneckRatio P π S := by
    have hbnn : 0 ≤ bottleneckRatio P π S := by
      rw [bottleneckRatio]
      refine div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
        (Finset.sum_nonneg fun x _ => (hpos x).le)
      rw [edgeMeasure]
      exact mul_nonneg (hpos x).le (hP.1 x y)
    refine mul_le_mul_of_nonneg_right ?_ hbnn
    exact_mod_cast hcon.le
  linarith [hle, hmem, hhalf, hmono, hT]

private lemma pow_nonneg_of_stochastic (P : Matrix V V ℝ) (hP : IsStochastic P) :
    ∀ (m : ℕ) (x y : V), 0 ≤ (P ^ m) x y := by
  intro m
  induction m with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

private lemma pow_pos_step (P : Matrix V V ℝ) (hP : IsStochastic P) {m : ℕ} {σ ρ τ : V}
    (h1 : 0 < (P ^ m) σ ρ) (h2 : 0 < P ρ τ) : 0 < (P ^ (m + 1)) σ τ := by
  rw [pow_succ, Matrix.mul_apply]
  refine lt_of_lt_of_le (mul_pos h1 h2) ?_
  exact Finset.single_le_sum (f := fun z => (P ^ m) σ z * P z τ)
    (fun z _ => mul_nonneg (pow_nonneg_of_stochastic P hP m σ z) (hP.1 z τ))
    (Finset.mem_univ ρ)

end Bottleneck

section Analytic

private lemma sinh_ge_self {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.sinh u - u) (Real.cosh t - 1) t := by
    intro t
    simpa using (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
  have hmono : Monotone (fun u : ℝ => Real.sinh u - u) := by
    refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
    rw [(hd t).deriv]
    linarith [Real.one_le_cosh t]
  have h := hmono hx
  simp only [Real.sinh_zero, sub_zero, zero_sub] at h
  linarith

private lemma sinh_sq_ge (x : ℝ) : x ^ 2 ≤ Real.sinh x ^ 2 := by
  rcases le_total 0 x with h | h
  · nlinarith [sinh_ge_self h]
  · have h1 : (0 : ℝ) ≤ -x := by linarith
    have h2 : -x ≤ Real.sinh (-x) := sinh_ge_self h1
    rw [Real.sinh_neg] at h2
    nlinarith

private lemma cosh_half (x : ℝ) : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x / 2)
  have h2 : 2 * (x / 2) = x := by ring
  rw [h2] at h
  have h3 := Real.cosh_sq_sub_sinh_sq (x / 2)
  linarith

private lemma sinh_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x + x ^ 3 / 6 ≤ Real.sinh x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.sinh u - u - u ^ 3 / 6)
      (Real.cosh t - 1 - t ^ 2 / 2) t := by
    intro t
    have h1 := (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    have h2 : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (3 * t ^ 2 / 6) t := by
      simpa using ((hasDerivAt_pow 3 t).div_const 6)
    have h3 := h1.sub h2
    convert h3 using 1
    ring
  have hmono : Monotone (fun u : ℝ => Real.sinh u - u - u ^ 3 / 6) := by
    refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
    rw [(hd t).deriv]
    have h1 := cosh_half t
    have h2 := sinh_sq_ge (t / 2)
    nlinarith
  have h := hmono hx
  simp only [Real.sinh_zero] at h
  norm_num at h
  linarith

private lemma cosh_ge_quartic {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 / 2 + x ^ 4 / 24 ≤ Real.cosh x := by
  have h1 : x / 2 + (x / 2) ^ 3 / 6 ≤ Real.sinh (x / 2) := sinh_ge_cubic (by linarith)
  have h2 : (0 : ℝ) ≤ x / 2 + (x / 2) ^ 3 / 6 := by positivity
  have h3 := cosh_half x
  nlinarith [sq_nonneg x, pow_nonneg hx 6]

private lemma exp_le_quad {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    Real.exp x ≤ 1 + x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound' hx0 hx (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The tilt parameter. -/
private def tiltA (α : ℝ) : ℝ := min 1 (Real.sqrt (α * (α - 1)))

private lemma tiltA_pos {α : ℝ} (hα : 1 < α) : 0 < tiltA α := by
  rw [tiltA]
  refine lt_min (by norm_num) ?_
  refine Real.sqrt_pos.mpr ?_
  nlinarith

private lemma tiltA_le_one (α : ℝ) : tiltA α ≤ 1 := min_le_left _ _

private lemma tiltA_sq_le {α : ℝ} (hα : 1 < α) : tiltA α ^ 2 ≤ α * (α - 1) := by
  rcases le_total (Real.sqrt (α * (α - 1))) 1 with h | h
  · have he : tiltA α = Real.sqrt (α * (α - 1)) := min_eq_right h
    rw [he, Real.sq_sqrt (by nlinarith)]
  · have he : tiltA α = 1 := min_eq_left h
    rw [he]
    have h2 : (1 : ℝ) ≤ Real.sqrt (α * (α - 1)) := h
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ α * (α - 1) by nlinarith), Real.sqrt_nonneg (α*(α-1))]

private lemma cosh_gt_exp {α : ℝ} (hα : 1 < α) :
    Real.exp (tiltA α ^ 2 / (2 * α)) < Real.cosh (tiltA α) := by
  set a := tiltA α with ha
  have ha0 : 0 < a := tiltA_pos hα
  have ha1 : a ≤ 1 := tiltA_le_one α
  have hasq : a ^ 2 ≤ α * (α - 1) := tiltA_sq_le hα
  have hαpos : (0 : ℝ) < α := by linarith
  have hx0 : 0 ≤ a ^ 2 / (2 * α) := by positivity
  have hx1 : a ^ 2 / (2 * α) ≤ 1 := by
    rw [div_le_one (by linarith)]
    nlinarith
  have hexp := exp_le_quad hx0 hx1
  have hcosh := cosh_ge_quartic ha0.le
  have hkey : 1 + a ^ 2 / (2 * α) + 3 / 4 * (a ^ 2 / (2 * α)) ^ 2
      < 1 + a ^ 2 / 2 + a ^ 4 / 24 := by
    have hq : (a ^ 2 / (2 * α)) ^ 2 = a ^ 4 / (4 * α ^ 2) := by
      field_simp
      ring
    rw [hq]
    set u : ℝ := a ^ 2 * (α - 1) / (2 * α) with hu
    have h1 : 2 * (a ^ 4 / (4 * α ^ 2)) ≤ u := by
      have he : 2 * (a ^ 4 / (4 * α ^ 2)) = a ^ 4 / (2 * α ^ 2) := by ring
      rw [hu, he, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hasq (show (0:ℝ) ≤ a ^ 2 * (2 * α) by positivity)]
    have h2 : a ^ 2 / (2 * α) + u = a ^ 2 / 2 := by
      rw [hu]
      field_simp
      ring
    have hpos : 0 < u := by
      rw [hu]
      exact div_pos (by nlinarith [pow_pos ha0 2]) (by linarith)
    have hc : (0 : ℝ) ≤ a ^ 4 / 24 := by positivity
    linarith
  linarith

/-- The exponential rate. -/
private def rate (α : ℝ) : ℝ := Real.log (Real.cosh (tiltA α)) - tiltA α ^ 2 / (2 * α)

private lemma rate_pos {α : ℝ} (hα : 1 < α) : 0 < rate α := by
  have h := cosh_gt_exp hα
  have hlog : Real.log (Real.exp (tiltA α ^ 2 / (2 * α)))
      < Real.log (Real.cosh (tiltA α)) :=
    Real.log_lt_log (Real.exp_pos _) h
  rw [Real.log_exp] at hlog
  rw [rate]
  linarith

private lemma cosh_pow (α : ℝ) (n : ℕ) :
    Real.cosh (tiltA α) ^ n
      = Real.exp ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α) := by
  rw [rate]
  have h : (n : ℝ) * (tiltA α ^ 2 / (2 * α))
      + (n : ℝ) * (Real.log (Real.cosh (tiltA α)) - tiltA α ^ 2 / (2 * α))
      = (n : ℝ) * Real.log (Real.cosh (tiltA α)) := by ring
  rw [h, Real.exp_nat_mul, Real.exp_log (Real.cosh_pos _)]

end Analytic


section CurieWeiss

variable {n : ℕ}

/-- The number of up-spins. -/
private def upC (σ : Fin n → Bool) : ℕ := (univ.filter fun v => σ v = true).card

/-- The magnetization. -/
private def magn (σ : Fin n → Bool) : ℝ := ∑ v, spin σ v

private lemma magn_eq (σ : Fin n → Bool) : magn σ = 2 * (upC σ : ℝ) - (n : ℝ) := by
  have h : ∀ v : Fin n, spin σ v = 2 * (if σ v = true then (1:ℝ) else 0) - 1 := by
    intro v
    cases h : σ v <;> simp [spin, h] <;> norm_num
  have hcount : (∑ v : Fin n, if σ v = true then (1:ℝ) else 0) = (upC σ : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, upC]
  rw [magn, Finset.sum_congr rfl fun v _ => h v, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private lemma sum_ne_split (f : Fin n → ℝ) (u : Fin n) :
    (∑ w, if u ≠ w then f w else 0) = (∑ w, f w) - f u := by
  have hfun : (fun w => if u ≠ w then f w else 0)
      = fun w => f w - (if w = u then f w else 0) := by
    funext w
    by_cases h : w = u
    · subst h; simp
    · rw [if_pos (fun hc => h hc.symm), if_neg h]; ring
  rw [Finset.sum_congr rfl fun w _ => congrFun hfun w, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ u f]
  simp

private lemma spin_sq (σ : Fin n → Bool) (v : Fin n) : spin σ v * spin σ v = 1 := by
  cases h : σ v <;> simp [spin, h]

private lemma energy_eq (σ : Fin n → Bool) :
    (∑ u : Fin n, ∑ w : Fin n,
        if (⊤ : SimpleGraph (Fin n)).Adj u w then spin σ u * spin σ w else 0)
      = magn σ ^ 2 - (n : ℝ) := by
  have hrow : ∀ u : Fin n,
      (∑ w : Fin n, if (⊤ : SimpleGraph (Fin n)).Adj u w then spin σ u * spin σ w else 0)
        = spin σ u * magn σ - 1 := by
    intro u
    have hcond : ∀ w : Fin n,
        (if (⊤ : SimpleGraph (Fin n)).Adj u w then spin σ u * spin σ w else 0)
          = if u ≠ w then spin σ u * spin σ w else 0 := by
      intro w
      by_cases h : u = w
      · rw [if_neg (by simp [h]), if_neg (by simp [h])]
      · rw [if_pos (by simpa using h), if_pos h]
    rw [Finset.sum_congr rfl fun w _ => hcond w,
      sum_ne_split (fun w => spin σ u * spin σ w) u, ← Finset.mul_sum, spin_sq]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [magn]
  ring

private lemma weight_eq (α : ℝ) (σ : Fin n → Bool) :
    isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      = Real.exp (α / (2 * (n : ℝ)) * (magn σ ^ 2 - (n : ℝ))) := by
  rw [isingWeight, energy_eq]
  congr 1
  ring

private lemma magn_flip (σ : Fin n → Bool) : magn (fun v => !(σ v)) = - magn σ := by
  rw [magn, magn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases h : σ v <;> simp [spin, h]

private lemma weight_flip (α : ℝ) (σ : Fin n → Bool) :
    isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) (fun v => !(σ v))
      = isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
  rw [weight_eq, weight_eq, magn_flip]
  congr 2
  ring

private lemma upC_flip (σ : Fin n → Bool) : upC (fun v => !(σ v)) = n - upC σ := by
  have hcompl : (univ.filter fun v : Fin n => (!(σ v)) = true)
      = (univ.filter fun v : Fin n => σ v = true)ᶜ := by
    ext v
    simp [Finset.mem_compl]
  rw [upC, hcompl, Finset.card_compl, Fintype.card_fin]
  rfl

/-- The `magnetization < 0` half. -/
private def Sneg (n : ℕ) : Finset (Fin n → Bool) := univ.filter fun σ => 2 * upC σ < n

/-- The boundary layer. -/
private def Bset (n : ℕ) : Finset (Fin n → Bool) :=
  univ.filter fun σ => 2 * upC σ < n ∧ n ≤ 2 * upC σ + 2

private lemma mem_Sneg (σ : Fin n → Bool) : σ ∈ Sneg n ↔ magn σ < 0 := by
  rw [Sneg, Finset.mem_filter, magn_eq]
  constructor
  · rintro ⟨-, h⟩
    have : (2 * upC σ : ℝ) < (n : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    have : (2 * upC σ : ℝ) < (n : ℝ) := by push_cast; push_cast at h; linarith
    exact_mod_cast this

private lemma mem_Bset (σ : Fin n → Bool) :
    σ ∈ Bset n ↔ (magn σ < 0 ∧ -2 ≤ magn σ) := by
  rw [Bset, Finset.mem_filter, magn_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    have e1 : (2 * upC σ : ℝ) < (n : ℝ) := by exact_mod_cast h1
    have e2 : (n : ℝ) ≤ (2 * upC σ : ℝ) + 2 := by exact_mod_cast h2
    push_cast at e1 e2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have : (2 * upC σ : ℝ) < (n : ℝ) := by push_cast; push_cast at h1; linarith
      exact_mod_cast this
    · have : (n : ℝ) ≤ (2 * upC σ : ℝ) + 2 := by push_cast; push_cast at h2; linarith
      exact_mod_cast this

private lemma Bset_subset : Bset n ⊆ Sneg n := by
  intro σ hσ
  rw [mem_Bset] at hσ
  rw [mem_Sneg]
  exact hσ.1

private lemma Sneg_nonempty (hn : 0 < n) : (Sneg n).Nonempty := by
  refine ⟨fun _ => false, ?_⟩
  rw [mem_Sneg, magn_eq]
  have h : upC (fun _ : Fin n => false) = 0 := by
    rw [upC]
    convert Finset.card_empty
    ext v
    simp
  rw [h]
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp
  linarith

private def gfun (a : ℝ) : Bool → ℝ := fun s => Real.exp (-(a * (if s then (1:ℝ) else -1)))

private lemma sum_prod_bool (g : Bool → ℝ) (n : ℕ) :
    ∑ σ : Fin n → Bool, ∏ v : Fin n, g (σ v) = (g true + g false) ^ n := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun (_ : Fin n) (s : Bool) => g s)
  rw [Fintype.piFinset_univ] at h
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Fintype.sum_bool g

private lemma sum_exp_magn (a : ℝ) (n : ℕ) :
    ∑ σ : Fin n → Bool, Real.exp (-(a * magn σ)) = (2 * Real.cosh a) ^ n := by
  have hterm : ∀ σ : Fin n → Bool,
      Real.exp (-(a * magn σ))
        = ∏ v : Fin n, Real.exp (-(a * spin σ v)) := by
    intro σ
    rw [← Real.exp_sum]
    congr 1
    rw [magn, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ]
  have hg : ∀ (σ : Fin n → Bool) (v : Fin n),
      Real.exp (-(a * spin σ v)) = gfun a (σ v) := by
    intro σ v
    rw [gfun, spin]
  rw [Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun v _ => hg σ v]
  rw [sum_prod_bool (gfun a) n]
  congr 1
  simp only [gfun, Real.cosh_eq]
  norm_num
  try ring

private lemma card_le_two_pow (T : Finset (Fin n → Bool)) : (T.card : ℝ) ≤ 2 ^ n := by
  have h1 : T.card ≤ Fintype.card (Fin n → Bool) := Finset.card_le_univ T
  have h2 : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun]
    simp
  rw [h2] at h1
  exact_mod_cast h1

private lemma num_bound (α : ℝ) (hα : 1 < α) (hn : 0 < n) :
    ∑ σ ∈ Bset n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      ≤ 2 ^ n * Real.exp (α / (2 * (n : ℝ)) * (4 - (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcoef : (0 : ℝ) < α / (2 * (n : ℝ)) := by positivity
  have hterm : ∀ σ ∈ Bset n,
      isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
        ≤ Real.exp (α / (2 * (n : ℝ)) * (4 - (n : ℝ))) := by
    intro σ hσ
    rw [weight_eq]
    refine Real.exp_le_exp.mpr ?_
    rw [mem_Bset] at hσ
    have hm : magn σ ^ 2 ≤ 4 := by nlinarith [hσ.1, hσ.2]
    nlinarith [hcoef]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_le_two_pow _) (Real.exp_pos _).le

private lemma den_bound (α : ℝ) (hα : 1 < α) (hn : 0 < n) :
    Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
        * ((2 * Real.cosh (tiltA α)) ^ n - 2 ^ n)
      ≤ ∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hαpos : (0 : ℝ) < α := by linarith
  set a := tiltA α with ha
  have ha0 : 0 < a := tiltA_pos hα
  -- pointwise lower bound on the weight
  have hpt : ∀ σ : Fin n → Bool,
      Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (a ^ 2 / (2 * α))))
          * Real.exp (-(a * magn σ))
        ≤ isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
    intro σ
    rw [weight_eq, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsq : 0 ≤ (α / (2 * (n : ℝ))) * (magn σ + (n : ℝ) * a / α) ^ 2 := by positivity
    have hexp : (α / (2 * (n : ℝ))) * (magn σ + (n : ℝ) * a / α) ^ 2
        = α / (2 * (n : ℝ)) * magn σ ^ 2 + a * magn σ + (n : ℝ) * (a ^ 2 / (2 * α)) := by
      field_simp
      try ring
    rw [hexp] at hsq
    have : α / (2 * (n : ℝ)) * (magn σ ^ 2 - (n : ℝ))
        = α / (2 * (n : ℝ)) * magn σ ^ 2 - α / 2 := by
      field_simp
      try ring
    rw [this]
    linarith
  -- the exponential sum over the negative half
  have hsplit : ∑ σ : Fin n → Bool, Real.exp (-(a * magn σ))
      = (∑ σ ∈ Sneg n, Real.exp (-(a * magn σ)))
        + ∑ σ ∈ (Sneg n)ᶜ, Real.exp (-(a * magn σ)) :=
    (Finset.sum_add_sum_compl (Sneg n) _).symm
  have hcompl : ∑ σ ∈ (Sneg n)ᶜ, Real.exp (-(a * magn σ)) ≤ 2 ^ n := by
    have hterm : ∀ σ ∈ (Sneg n)ᶜ, Real.exp (-(a * magn σ)) ≤ 1 := by
      intro σ hσ
      rw [Finset.mem_compl, mem_Sneg] at hσ
      push_neg at hσ
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [ha0.le]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_le_two_pow _
  have hlow : (2 * Real.cosh a) ^ n - 2 ^ n
      ≤ ∑ σ ∈ Sneg n, Real.exp (-(a * magn σ)) := by
    rw [← sum_exp_magn a n, hsplit]
    linarith
  -- combine
  have hmain : ∑ σ ∈ Sneg n,
      (Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (a ^ 2 / (2 * α))))
        * Real.exp (-(a * magn σ)))
      ≤ ∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ :=
    Finset.sum_le_sum fun σ _ => hpt σ
  refine le_trans ?_ hmain
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hlow (by positivity)


/-! ### The Glauber chain on the complete graph -/

private lemma isingWeight_pos (α : ℝ) (σ : Fin n → Bool) :
    0 < isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := Real.exp_pos _

private lemma isingZ_pos (α : ℝ) :
    (0 : ℝ) < ∑ η : Fin n → Bool, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) η :=
  Finset.sum_pos (fun η _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

private lemma isingDist_pos (α : ℝ) (σ : Fin n → Bool) :
    0 < isingDist (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
  rw [isingDist]
  exact div_pos (Real.exp_pos _) (isingZ_pos α)

private lemma isingDist_isDist (α : ℝ) :
    IsDist (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) := by
  refine ⟨fun σ => (isingDist_pos α σ).le, ?_⟩
  simp only [isingDist]
  rw [← sum_div_const, div_self (ne_of_gt (isingZ_pos α))]

private lemma glauber_pos_of_agree {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Fin n → S) → ℝ) (hpos : ∀ x, 0 < π x) (hn : 0 < n)
    (σ τ : Fin n → S) (v : Fin n) (h : ∀ w, w ≠ v → τ w = σ w) :
    0 < glauber π σ τ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hN : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos
    exact_mod_cast this
  rw [glauber]
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos' (fun w _ => ?_) ⟨v, Finset.mem_univ v, ?_⟩
  · split_ifs
    · exact le_of_lt (div_pos (hpos τ)
        (Finset.sum_pos (fun z _ => hpos z) ⟨σ, by simp⟩))
    · exact le_refl 0
  · rw [if_pos h]
    exact div_pos (hpos τ) (Finset.sum_pos (fun z _ => hpos z) ⟨σ, by simp⟩)

private lemma glauber_irred_fin {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Fin n → S) → ℝ) (hpos : ∀ x, 0 < π x) (hn : 0 < n)
    (hst : IsStochastic (glauber π)) : Irreducible (glauber π) := by
  intro σ τ
  refine ⟨n, ?_⟩
  have key : ∀ k : ℕ, k ≤ n →
      0 < ((glauber π) ^ k) σ (fun v : Fin n => if v.val < k then τ v else σ v) := by
    intro k
    induction k with
    | zero =>
        intro _
        have h0 : (fun v : Fin n => if v.val < 0 then τ v else σ v) = σ := by
          funext v
          rw [if_neg (Nat.not_lt_zero _)]
        rw [pow_zero, h0, Matrix.one_apply_eq]
        norm_num
    | succ k ih =>
        intro hk
        have hklt : k < n := by omega
        have h1 := ih (by omega)
        have h2 : 0 < glauber π (fun v : Fin n => if v.val < k then τ v else σ v)
            (fun v : Fin n => if v.val < k + 1 then τ v else σ v) := by
          refine glauber_pos_of_agree π hpos hn _ _ ⟨k, hklt⟩ ?_
          intro w hw
          have hne : w.val ≠ k := fun hc => hw (Fin.ext hc)
          by_cases hlt : w.val < k
          · rw [if_pos (by omega), if_pos hlt]
          · rw [if_neg (by omega), if_neg hlt]
        exact pow_pos_step (glauber π) hst h1 h2
  have hfin := key n (le_refl n)
  have hend : (fun v : Fin n => if v.val < n then τ v else σ v) = τ := by
    funext v
    rw [if_pos v.isLt]
  rwa [hend] at hfin

private lemma glauber_self_pos {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Fin n → S) → ℝ) (hpos : ∀ x, 0 < π x) (hn : 0 < n) (σ : Fin n → S) :
    0 < glauber π σ σ :=
  glauber_pos_of_agree π hpos hn σ σ ⟨0, hn⟩ (fun w _ => rfl)

private lemma glauber_aperiodic_fin {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Fin n → S) → ℝ) (hpos : ∀ x, 0 < π x) (hn : 0 < n) : Aperiodic (glauber π) := by
  intro x
  have h1 : (1 : ℕ) ∈ returnSet (glauber π) x := by
    refine ⟨le_refl 1, ?_⟩
    rw [pow_one]
    exact glauber_self_pos π hpos hn x
  have hset : {d : ℕ | ∀ t ∈ returnSet (glauber π) x, d ∣ t} = {1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Nat.dvd_one.mp (h 1 h1)
    · intro h t _
      rw [h]
      exact one_dvd t
  rw [period, hset, csSup_singleton]

private lemma glauber_support {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Fin n → S) → ℝ) (x y : Fin n → S) (h : glauber π x y ≠ 0) :
    ∃ v : Fin n, ∀ w : Fin n, w ≠ v → y w = x w := by
  by_contra hc
  push_neg at hc
  refine h ?_
  rw [glauber, mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun v _ => ?_
  obtain ⟨w, hw, hne⟩ := hc v
  exact if_neg (fun hcon => hne (hcon w hw))

private lemma magn_diff_le (σ τ : Fin n → Bool) (v : Fin n)
    (h : ∀ w : Fin n, w ≠ v → τ w = σ w) : magn τ ≤ magn σ + 2 := by
  have hterm : ∀ w : Fin n, spin τ w - spin σ w = if w = v then spin τ v - spin σ v else 0 := by
    intro w
    by_cases hw : w = v
    · rw [if_pos hw, hw]
    · rw [if_neg hw]
      simp only [spin, h w hw]
      ring
  have hsum : magn τ - magn σ = spin τ v - spin σ v := by
    rw [magn, magn, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_ite_eq' Finset.univ v]
    simp
  have hb1 : spin τ v ≤ 1 := by cases h : τ v <;> simp [spin, h] <;> norm_num
  have hb2 : -1 ≤ spin σ v := by cases h : σ v <;> simp [spin, h] <;> norm_num
  linarith [hsum]


private lemma glauber_stoch_ising (α : ℝ) (hn : 0 < n) :
    IsStochastic (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := glauber_stationary (isingDist (⊤ : SimpleGraph (Fin n)) (α / n))
    (isingDist_isDist α)
  exact ⟨h.1, fun x => h.2.1 x (isingDist_pos α x)⟩

private lemma glauber_stat_ising (α : ℝ) (hn : 0 < n) :
    IsStationary (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
      (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (glauber_stationary (isingDist (⊤ : SimpleGraph (Fin n)) (α / n))
    (isingDist_isDist α)).2.2.2

private lemma mix_nonempty (α : ℝ) (hn : 0 < n) :
    {t : ℕ | distStationary (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
      (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) t ≤ 1 / 4}.Nonempty := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨c, ⟨hc0, hc1⟩, C, hC, hbd⟩ := convergence_theorem
    (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n))) (glauber_stoch_ising α hn)
    (glauber_irred_fin _ (isingDist_pos α) hn (glauber_stoch_ising α hn))
    (glauber_aperiodic_fin _ (isingDist_pos α) hn)
    (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) (glauber_stat_ising α hn)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1 / 4 / C by positivity) hc1
  refine ⟨t, ?_⟩
  refine le_trans (hbd t) ?_
  calc C * c ^ t ≤ C * (1 / 4 / C) := mul_le_mul_of_nonneg_left ht.le hC.le
    _ = 1 / 4 := by field_simp

private lemma Q_le (α : ℝ) (hα : 1 < α) (hn : 0 < n) :
    ∑ x ∈ Sneg n, ∑ y ∈ (Sneg n)ᶜ,
        edgeMeasure (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
          (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) x y
      ≤ ∑ x ∈ Bset n, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x := by
  have hst := glauber_stoch_ising (n := n) α hn
  have hzero : ∀ x ∈ Sneg n, x ∉ Bset n →
      (∑ y ∈ (Sneg n)ᶜ, edgeMeasure (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
        (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) x y) = 0 := by
    intro x hx hxB
    rw [mem_Sneg] at hx
    have hlt : magn x < -2 := by
      by_contra hc
      push_neg at hc
      exact hxB ((mem_Bset x).mpr ⟨hx, hc⟩)
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [Finset.mem_compl, mem_Sneg] at hy
    push_neg at hy
    rw [edgeMeasure]
    have hP : glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) x y = 0 := by
      by_contra hne
      obtain ⟨v, hv⟩ := glauber_support _ x y hne
      have := magn_diff_le x y v hv
      linarith
    rw [hP, mul_zero]
  rw [← Finset.sum_subset (Bset_subset (n := n)) hzero]
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : ∑ y ∈ (Sneg n)ᶜ, edgeMeasure (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
        (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) x y
      = isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x
        * ∑ y ∈ (Sneg n)ᶜ, glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) x y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => rfl
  rw [h1]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (isingDist_pos α x).le) (le_of_eq (mul_one _))
  rw [← hst.2 x]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hst.1 x y)

/-- The positive-magnetization half. -/
private def Spos (n : ℕ) : Finset (Fin n → Bool) := univ.filter fun σ => n < 2 * upC σ

private lemma mem_Spos (σ : Fin n → Bool) : σ ∈ Spos n ↔ 0 < magn σ := by
  rw [Spos, Finset.mem_filter, magn_eq]
  constructor
  · rintro ⟨-, h⟩
    have : (n : ℝ) < (2 * upC σ : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    have : (n : ℝ) < (2 * upC σ : ℝ) := by push_cast; push_cast at h; linarith
    exact_mod_cast this

private lemma sum_Sneg_le (α : ℝ) :
    ∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      ≤ ∑ σ ∈ (Sneg n)ᶜ, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
  have hbij : ∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      = ∑ σ ∈ Spos n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
    refine Finset.sum_nbij' (fun σ => fun v => !(σ v)) (fun σ => fun v => !(σ v)) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [mem_Sneg] at hσ
      rw [mem_Spos, magn_flip]
      linarith
    · intro σ hσ
      rw [mem_Spos] at hσ
      rw [mem_Sneg, magn_flip]
      linarith
    · intro σ _
      funext v
      simp
    · intro σ _
      funext v
      simp
    · intro σ _
      exact (weight_flip α σ).symm
  rw [hbij]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun σ _ _ => (isingWeight_pos α σ).le)
  intro σ hσ
  rw [mem_Spos] at hσ
  rw [Finset.mem_compl, mem_Sneg]
  push_neg
  linarith

private lemma pi_compl_ge_half (α : ℝ) :
    (2 : ℝ)⁻¹ ≤ ∑ x ∈ (Sneg n)ᶜ, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x := by
  have hZ := isingZ_pos (n := n) α
  have htot : (∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ)
      + ∑ σ ∈ (Sneg n)ᶜ, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      = ∑ σ : Fin n → Bool, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ :=
    Finset.sum_add_sum_compl _ _
  have hle := sum_Sneg_le (n := n) α
  have hhalf : (∑ σ : Fin n → Bool, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ) / 2
      ≤ ∑ σ ∈ (Sneg n)ᶜ, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
    linarith
  have hpi : ∑ x ∈ (Sneg n)ᶜ, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x
      = (∑ σ ∈ (Sneg n)ᶜ, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ)
        / ∑ σ : Fin n → Bool, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
    rw [sum_div_const]
    exact Finset.sum_congr rfl fun σ _ => rfl
  rw [hpi, le_div_iff₀ hZ]
  linarith


private lemma weight_ratio_bound (α : ℝ) (hα : 1 < α) (hn : 0 < n)
    (hcosh : (2 : ℝ) ≤ Real.cosh (tiltA α) ^ n) :
    ∑ σ ∈ Bset n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ
      ≤ 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))
        * ∑ σ ∈ Sneg n, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hαpos : (0 : ℝ) < α := by linarith
  have hK0 : (0 : ℝ) < 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α)) := by positivity
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  -- the tail of the tilted binomial sum
  have hi : (2 : ℝ) ^ n * Real.cosh (tiltA α) ^ n / 2
      ≤ (2 * Real.cosh (tiltA α)) ^ n - 2 ^ n := by
    rw [mul_pow]
    nlinarith [h2pow, hcosh]
  have e1 : Real.exp (-((n : ℝ) * rate α)) * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
      * Real.exp ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add,
      show -((n : ℝ) * rate α) + -((n : ℝ) * (tiltA α ^ 2 / (2 * α)))
        + ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α) = 0 from by ring]
    exact Real.exp_zero
  have heq : 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))
      * (Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
        * ((2 : ℝ) ^ n * Real.cosh (tiltA α) ^ n / 2))
      = (2 : ℝ) ^ n * (Real.exp (2 * α) * Real.exp (-(α / 2))) := by
    rw [cosh_pow α n,
      show 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))
        * (Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
          * ((2 : ℝ) ^ n
             * Real.exp ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α) / 2))
        = ((2 : ℝ) ^ n * (Real.exp (2 * α) * Real.exp (-(α / 2))))
          * (Real.exp (-((n : ℝ) * rate α))
             * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
             * Real.exp ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α)) from by ring,
      e1, mul_one]
  -- the numerator side
  have hnum : (2 : ℝ) ^ n * Real.exp (α / (2 * (n : ℝ)) * (4 - (n : ℝ)))
      ≤ (2 : ℝ) ^ n * (Real.exp (2 * α) * Real.exp (-(α / 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ h2pow.le
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hdiv : α / (2 * (n : ℝ)) * (4 - (n : ℝ)) = 2 * α / (n : ℝ) - α / 2 := by
      field_simp
      ring
    rw [hdiv]
    have h2a : 2 * α / (n : ℝ) ≤ 2 * α := by
      rw [div_le_iff₀ hnR]
      nlinarith
    linarith
  -- combine
  have hstep : (2 : ℝ) ^ n * Real.exp (α / (2 * (n : ℝ)) * (4 - (n : ℝ)))
      ≤ 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))
        * (Real.exp (-(α / 2)) * Real.exp (-((n : ℝ) * (tiltA α ^ 2 / (2 * α))))
          * ((2 * Real.cosh (tiltA α)) ^ n - 2 ^ n)) := by
    refine le_trans hnum ?_
    rw [← heq]
    refine mul_le_mul_of_nonneg_left ?_ hK0.le
    refine mul_le_mul_of_nonneg_left hi ?_
    positivity
  refine le_trans (num_bound α hα hn) (le_trans hstep ?_)
  exact mul_le_mul_of_nonneg_left (den_bound α hα hn) hK0.le

private lemma bottleneck_bound (α : ℝ) (hα : 1 < α) (hn : 0 < n)
    (hcosh : (2 : ℝ) ≤ Real.cosh (tiltA α) ^ n) :
    bottleneckRatio (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
        (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) (Sneg n)
      ≤ 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α)) := by
  have hZ := isingZ_pos (n := n) α
  have hK0 : (0 : ℝ) < 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α)) := by positivity
  have hSpos : (0 : ℝ) < ∑ x ∈ Sneg n, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x :=
    Finset.sum_pos (fun x _ => isingDist_pos α x) (Sneg_nonempty hn)
  have hpiW : ∀ T : Finset (Fin n → Bool),
      ∑ x ∈ T, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x
        = (∑ x ∈ T, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) x)
          / ∑ σ : Fin n → Bool, isingWeight (⊤ : SimpleGraph (Fin n)) (α / n) σ := by
    intro T
    rw [sum_div_const]
    exact Finset.sum_congr rfl fun σ _ => rfl
  have hBS : ∑ x ∈ Bset n, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x
      ≤ 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))
        * ∑ x ∈ Sneg n, isingDist (⊤ : SimpleGraph (Fin n)) (α / n) x := by
    rw [hpiW, hpiW, mul_div_assoc', div_le_div_iff₀ hZ hZ]
    exact mul_le_mul_of_nonneg_right (weight_ratio_bound α hα hn hcosh) hZ.le
  rw [bottleneckRatio, div_le_iff₀ hSpos]
  exact le_trans (Q_le α hα hn) hBS

end CurieWeiss



end

end MarkovMixing

open MarkovMixing

/-- **Theorem 15.3(ii)** (LPW): for the Glauber dynamics of the Ising model
on the complete graph at `β = α/n` with `α > 1`, the mixing time is
exponentially large: there are `r(α) > 0` and `C > 0` with
`t_mix ≥ C e^{r(α) n}` for all large `n`. -/
theorem solution (α : ℝ) (hα : 1 < α) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * Real.exp (r * n) ≤
        (tMix (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
          (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) : ℝ) := by
  have hrate := rate_pos hα
  have hαpos : (0 : ℝ) < α := by linarith
  refine ⟨rate α / 2, by linarith, 1, one_pos,
    ⌈(2 * α + Real.log 16) / (rate α / 2)⌉₊ + 1, ?_⟩
  intro n hn
  have hr : (0 : ℝ) < rate α / 2 := by linarith
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- the size condition on `n`
  have hnbig : (2 * α + Real.log 16) / (rate α / 2) < (n : ℝ) := by
    have h1 : (2 * α + Real.log 16) / (rate α / 2)
        ≤ (⌈(2 * α + Real.log 16) / (rate α / 2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(2 * α + Real.log 16) / (rate α / 2)⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hrn : 2 * α + Real.log 16 < rate α / 2 * (n : ℝ) := by
    rw [div_lt_iff₀ hr] at hnbig
    linarith
  have hrn0 : (0 : ℝ) ≤ rate α / 2 * (n : ℝ) := by positivity
  -- the tilted cosine is already large
  have hcosh : (2 : ℝ) ≤ Real.cosh (tiltA α) ^ n := by
    rw [cosh_pow α n]
    have hlog2 : Real.log 2 ≤ (n : ℝ) * rate α := by
      have hl16 : (0 : ℝ) ≤ Real.log 16 := Real.log_nonneg (by norm_num)
      have hl2 : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      nlinarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) * (tiltA α ^ 2 / (2 * α)) := by positivity
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((n : ℝ) * (tiltA α ^ 2 / (2 * α)) + (n : ℝ) * rate α) :=
          Real.exp_le_exp.mpr (by linarith)
  -- the bottleneck ratio is exponentially small
  have hbn := bottleneck_bound (n := n) α hα hn0 hcosh
  have hK0 : (0 : ℝ) < 2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α)) := by positivity
  -- the target step count
  set T : ℕ := ⌈Real.exp (rate α / 2 * (n : ℝ))⌉₊ with hTdef
  have hTle : (T : ℝ) < Real.exp (rate α / 2 * (n : ℝ)) + 1 := by
    rw [hTdef]
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hTK : (T : ℝ) * (2 * Real.exp (2 * α) * Real.exp (-((n : ℝ) * rate α))) < 1 / 4 := by
    have he1 : Real.exp (-((n : ℝ) * rate α))
        = Real.exp (-(rate α / 2 * (n : ℝ))) * Real.exp (-(rate α / 2 * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hEpos : (0 : ℝ) < Real.exp (rate α / 2 * (n : ℝ)) := Real.exp_pos _
    have hEinv : Real.exp (-(rate α / 2 * (n : ℝ))) = (Real.exp (rate α / 2 * (n : ℝ)))⁻¹ := by
      rw [Real.exp_neg]
    have hbig : 16 * Real.exp (2 * α) < Real.exp (rate α / 2 * (n : ℝ)) := by
      have h16 : (16 : ℝ) = Real.exp (Real.log 16) := (Real.exp_log (by norm_num)).symm
      rw [h16, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [he1, hEinv]
    have hstep : (T : ℝ) * (2 * Real.exp (2 * α)
        * ((Real.exp (rate α / 2 * (n : ℝ)))⁻¹ * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹))
        < (Real.exp (rate α / 2 * (n : ℝ)) + 1) * (2 * Real.exp (2 * α)
          * ((Real.exp (rate α / 2 * (n : ℝ)))⁻¹ * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹)) := by
      refine mul_lt_mul_of_pos_right hTle ?_
      positivity
    refine lt_of_lt_of_le hstep ?_
    have hE1 : (1 : ℝ) ≤ Real.exp (rate α / 2 * (n : ℝ)) :=
      Real.one_le_exp hrn0
    have key : (Real.exp (rate α / 2 * (n : ℝ)) + 1) * (2 * Real.exp (2 * α)
        * ((Real.exp (rate α / 2 * (n : ℝ)))⁻¹ * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹))
        ≤ 4 * Real.exp (2 * α) * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹ := by
      rw [← sub_nonneg]
      have hinv : (0 : ℝ) < (Real.exp (rate α / 2 * (n : ℝ)))⁻¹ := by positivity
      have hid : 4 * Real.exp (2 * α) * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹
          - (Real.exp (rate α / 2 * (n : ℝ)) + 1) * (2 * Real.exp (2 * α)
            * ((Real.exp (rate α / 2 * (n : ℝ)))⁻¹ * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹))
          = 2 * Real.exp (2 * α) * (Real.exp (rate α / 2 * (n : ℝ)))⁻¹
            * (1 - (Real.exp (rate α / 2 * (n : ℝ)))⁻¹) := by
        field_simp
        ring
      rw [hid]
      have h1inv : (Real.exp (rate α / 2 * (n : ℝ)))⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact hE1
      have : (0 : ℝ) ≤ 1 - (Real.exp (rate α / 2 * (n : ℝ)))⁻¹ := by linarith
      positivity
    refine le_trans key ?_
    rw [mul_inv_le_iff₀ hEpos]
    nlinarith [hbig, Real.exp_pos (2*α)]
  -- conclude
  have hfin : T ≤ tMix (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
      (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) := by
    refine bottleneck_tmix _ (glauber_stoch_ising α hn0) _ (isingDist_pos α)
      (glauber_stat_ising α hn0) (Sneg n) (Sneg_nonempty hn0) (pi_compl_ge_half α)
      (mix_nonempty α hn0) T ?_
    refine lt_of_le_of_lt ?_ hTK
    exact mul_le_mul_of_nonneg_left hbn (Nat.cast_nonneg T)
  have hle : Real.exp (rate α / 2 * (n : ℝ)) ≤ (T : ℝ) := Nat.le_ceil _
  rw [one_mul]
  exact le_trans hle (by exact_mod_cast hfin)
