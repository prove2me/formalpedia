-- Prove2me | solution 1 for MarkovMixing.ising_cycle
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T02:34:10.13675+00:00
-- url     : https://prove2.me/submissions/db8f533b-f73f-4892-b6cd-408d427167ad

import Definitions.Def_mm_ising
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_ising_high_temperature
import Theorems.Thm_MarkovMixing_glauber_stationary
import Theorems.Thm_MarkovMixing_distinguishing_statistic_nondegenerate
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Mixing of the Ising Glauber dynamics on the cycle (LPW Theorem 15.4)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Ising

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
variable (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ)

/-- The set of sites where two configurations disagree. -/
private def diffSet (σ τ : Vv → Bool) : Finset Vv :=
  univ.filter fun v => σ v ≠ τ v

private lemma mem_diffSet (σ τ : Vv → Bool) (v : Vv) : v ∈ diffSet σ τ ↔ σ v ≠ τ v := by
  simp [diffSet]

/-- The integer spin `±1`. -/
private def sgnZ (b : Bool) : ℤ := if b then 1 else -1

private lemma spin_eq (σ : Vv → Bool) (v : Vv) : spin σ v = ((sgnZ (σ v) : ℤ) : ℝ) := by
  cases h : σ v <;> simp [spin, sgnZ, h]

/-- The integer local field `∑_{w ~ v} σ(w)`. -/
private def Sz (σ : Vv → Bool) (v : Vv) : ℤ :=
  ∑ w, if G.Adj v w then sgnZ (σ w) else 0

private lemma Sz_real (σ : Vv → Bool) (v : Vv) :
    ((Sz G σ v : ℤ) : ℝ) = ∑ w, if G.Adj v w then spin σ w else 0 := by
  simp only [Sz, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h, spin_eq]
  · rw [if_neg h, if_neg h, Int.cast_zero]

private lemma Sz_sub_degree_even (σ : Vv → Bool) (v : Vv) :
    (2 : ℤ) ∣ Sz G σ v - (G.degree v : ℤ) := by
  have hdeg : ((G.degree v : ℕ) : ℤ) = ∑ w : Vv, if G.Adj v w then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    have : (univ.filter fun w : Vv => G.Adj v w) = G.neighborFinset v := by
      ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [this, Finset.sum_const, SimpleGraph.degree, nsmul_eq_mul, mul_one]
  rw [hdeg, Sz, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h]
    cases hw : σ w <;> simp [sgnZ, hw]
  · rw [if_neg h, if_neg h]; simp

private lemma Sz_diff_dvd (σ τ : Vv → Bool) (v : Vv) : (2 : ℤ) ∣ (Sz G σ v - Sz G τ v) := by
  have h1 := Sz_sub_degree_even G σ v
  have h2 := Sz_sub_degree_even G τ v
  omega

private lemma Sz_diff_bound (σ τ : Vv → Bool) (v : Vv) :
    |Sz G σ v - Sz G τ v| ≤ 2 * ((G.neighborFinset v ∩ diffSet σ τ).card : ℤ) := by
  classical
  have hsub : Sz G σ v - Sz G τ v
      = ∑ w : Vv, (if G.Adj v w then sgnZ (σ w) - sgnZ (τ w) else 0) := by
    rw [Sz, Sz, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj v w <;> simp [h]
  rw [hsub]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ w : Vv, |if G.Adj v w then sgnZ (σ w) - sgnZ (τ w) else 0|
      ≤ 2 * (if w ∈ G.neighborFinset v ∩ diffSet σ τ then (1 : ℤ) else 0) := by
    intro w
    by_cases h : G.Adj v w
    · rw [if_pos h]
      by_cases h2 : σ w = τ w
      · rw [h2, sub_self]
        simp only [abs_zero]
        split_ifs <;> norm_num
      · have : w ∈ G.neighborFinset v ∩ diffSet σ τ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_diffSet]
          exact ⟨h, h2⟩
        rw [if_pos this]
        cases hs : σ w <;> cases ht : τ w <;> simp [sgnZ, hs, ht] <;> omega
    · rw [if_neg h]
      simp
      positivity
  refine le_trans (Finset.sum_le_sum fun w _ => hterm w) ?_
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-- The part of the energy not involving the site `v`. -/
private def offPart (σ : Vv → Bool) (v : Vv) : ℝ :=
  ∑ u ∈ univ.erase v, ∑ w ∈ univ.erase v, if G.Adj u w then spin σ u * spin σ w else 0

private lemma spin_update_ne (σ : Vv → Bool) (v : Vv) (s : Bool) {u : Vv} (h : u ≠ v) :
    spin (Function.update σ v s) u = spin σ u := by
  simp [spin, Function.update_apply, h]

private lemma spin_update_self (σ : Vv → Bool) (v : Vv) (s : Bool) :
    spin (Function.update σ v s) v = ((sgnZ s : ℤ) : ℝ) := by
  cases s <;> simp [spin, sgnZ]

private lemma offPart_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    offPart G (Function.update σ v s) v = offPart G σ v := by
  simp only [offPart]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
  rw [spin_update_ne σ v s (Finset.ne_of_mem_erase hu),
    spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]

private lemma energy_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    (∑ u : Vv, ∑ w : Vv, if G.Adj u w then
        spin (Function.update σ v s) u * spin (Function.update σ v s) w else 0)
      = 2 * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ) + offPart G σ v := by
  classical
  set σ' := Function.update σ v s with hσ'
  set c : ℝ := ((sgnZ s : ℤ) : ℝ) with hc
  have hrow : ∀ u : Vv, u ≠ v →
      (∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0)
        = (if G.Adj u v then spin σ u * c else 0)
          + ∑ w ∈ univ.erase v, (if G.Adj u w then spin σ u * spin σ w else 0) := by
    intro u hu
    rw [← Finset.add_sum_erase _
      (fun w => if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
    congr 1
    · by_cases h : G.Adj u v
      · rw [if_pos h, if_pos h, spin_update_ne σ v s hu, hσ', spin_update_self]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [spin_update_ne σ v s hu, spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]
  have hv : (∑ w : Vv, if G.Adj v w then spin σ' v * spin σ' w else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj v w
    · have hwv : w ≠ v := fun hh => G.irrefl (hh ▸ h)
      rw [if_pos h, if_pos h, hσ', spin_update_self, spin_update_ne σ v s hwv]
    · rw [if_neg h, if_neg h, mul_zero]
  have hcol : (∑ u ∈ univ.erase v, if G.Adj u v then spin σ u * c else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    rw [← Finset.add_sum_erase _ (fun u => c * if G.Adj v u then spin σ u else 0)
      (Finset.mem_univ v)]
    have hvv : ¬ G.Adj v v := G.irrefl
    rw [if_neg hvv, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos (G.symm h)]; ring
    · rw [if_neg h, if_neg (fun hh => h (G.symm hh)), mul_zero]
  rw [← Finset.add_sum_erase _
    (fun u => ∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
  rw [hv, Finset.sum_congr rfl (fun u hu => hrow u (Finset.ne_of_mem_erase hu)),
    Finset.sum_add_distrib, hcol]
  simp only [offPart]
  ring

private lemma weight_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    isingWeight G β (Function.update σ v s)
      = Real.exp (β * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
  rw [isingWeight, energy_update, ← Real.exp_add]
  congr 1
  ring

/-- The conditional probability of the spin `+1` at `v` given the rest. -/
private def pT (σ : Vv → Bool) (v : Vv) : ℝ :=
  (1 + Real.tanh (β * ((Sz G σ v : ℤ) : ℝ))) / 2

/-- The conditional distribution of the spin at `v` given the rest. -/
private def pB (σ : Vv → Bool) (v : Vv) (s : Bool) : ℝ :=
  if s then pT G β σ v else 1 - pT G β σ v

private lemma tanh_lt_one' (x : ℝ) : |Real.tanh x| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x),
    div_lt_one (Real.cosh_pos x)]
  have h := Real.cosh_sq x
  have h2 : Real.sinh x ^ 2 < Real.cosh x ^ 2 := by nlinarith [Real.cosh_pos x]
  nlinarith [abs_nonneg (Real.sinh x), sq_abs (Real.sinh x), Real.cosh_pos x]

private lemma pB_nonneg (σ : Vv → Bool) (v : Vv) (s : Bool) : 0 ≤ pB G β σ v s := by
  have h := abs_lt.mp (tanh_lt_one' (β * ((Sz G σ v : ℤ) : ℝ)))
  cases s <;> simp only [pB, pT, if_true, if_false, Bool.false_eq_true] <;> linarith [h.1, h.2]

private lemma pB_add (σ : Vv → Bool) (v : Vv) :
    pB G β σ v true + pB G β σ v false = 1 := by
  simp only [pB]
  norm_num

private lemma exp_ratio (x : ℝ) :
    Real.exp x / (Real.exp x + Real.exp (-x)) = (1 + Real.tanh x) / 2 := by
  have h : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h2 : (Real.exp x + Real.exp (-x)) / 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma exp_ratio' (x : ℝ) :
    Real.exp (-x) / (Real.exp x + Real.exp (-x)) = 1 - (1 + Real.tanh x) / 2 := by
  have h : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h2 : (Real.exp x + Real.exp (-x)) / 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma pB_eq_exp (σ : Vv → Bool) (v : Vv) (s : Bool) :
    pB G β σ v s
      = Real.exp (β * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        / (Real.exp (β * ((Sz G σ v : ℤ) : ℝ)) + Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ)))) := by
  cases s
  · rw [show β * ((sgnZ false : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
        = -(β * ((Sz G σ v : ℤ) : ℝ)) from by simp [sgnZ], exp_ratio']
    rfl
  · rw [show β * ((sgnZ true : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
        = β * ((Sz G σ v : ℤ) : ℝ) from by simp [sgnZ], exp_ratio]
    rfl

private lemma isingWeight_pos (σ : Vv → Bool) : 0 < isingWeight G β σ := Real.exp_pos _

private lemma agree_iff (σ z : Vv → Bool) (v : Vv) :
    (∀ w : Vv, w ≠ v → z w = σ w) ↔ z = Function.update σ v (z v) := by
  constructor
  · intro h
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · rw [Function.update_apply, if_neg hw]
      exact h w hw
  · intro h w hw
    rw [h, Function.update_apply, if_neg hw]

private lemma update_ne (σ : Vv → Bool) (v : Vv) :
    Function.update σ v true ≠ Function.update σ v false := by
  intro h
  have := congrFun h v
  simp at this

private lemma filter_pair (σ : Vv → Bool) (v : Vv) :
    (univ.filter fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = σ w)
      = {Function.update σ v true, Function.update σ v false} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [agree_iff]
  constructor
  · intro h
    cases hz : z v
    · right; rw [h, hz]
    · left; rw [h, hz]
  · rintro (h | h) <;> rw [h] <;> simp

private lemma cond_ratio (σ τ : Vv → Bool) (v : Vv) (h : ∀ w : Vv, w ≠ v → τ w = σ w) :
    isingWeight G β τ /
        (isingWeight G β (Function.update σ v true)
          + isingWeight G β (Function.update σ v false))
      = pB G β σ v (τ v) := by
  have hτ : τ = Function.update σ v (τ v) := (agree_iff σ τ v).mp h
  have h1 : isingWeight G β τ
      = Real.exp (β * ((sgnZ (τ v) : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    conv_lhs => rw [hτ]
    exact weight_update G β σ v (τ v)
  have h2 : isingWeight G β (Function.update σ v true)
      = Real.exp (β * ((Sz G σ v : ℤ) : ℝ)) * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    rw [weight_update, show β * ((sgnZ true : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
      = β * ((Sz G σ v : ℤ) : ℝ) from by simp [sgnZ]]
  have h3 : isingWeight G β (Function.update σ v false)
      = Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ))) * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    rw [weight_update, show β * ((sgnZ false : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
      = -(β * ((Sz G σ v : ℤ) : ℝ)) from by simp [sgnZ]]
  rw [h1, h2, h3, pB_eq_exp]
  have hE : (0 : ℝ) < Real.exp (β * 2⁻¹ * offPart G σ v) := Real.exp_pos _
  have hd : (0 : ℝ) < Real.exp (β * ((Sz G σ v : ℤ) : ℝ))
      + Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ))) := by positivity
  field_simp
  try ring

private lemma glauber_apply [Nonempty Vv] (σ τ : Vv → Bool) :
    glauber (isingDist G β) σ τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv,
          (if ∀ w : Vv, w ≠ v → τ w = σ w then pB G β σ v (τ v) else 0) := by
  classical
  have hZ : (0 : ℝ) < ∑ η : Vv → Bool, isingWeight G β η := by
    refine Finset.sum_pos (fun η _ => Real.exp_pos _) ?_
    exact ⟨fun _ => true, Finset.mem_univ _⟩
  rw [glauber]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : ∀ w : Vv, w ≠ v → τ w = σ w
  · rw [if_pos h, if_pos h, filter_pair, Finset.sum_pair (update_ne σ v)]
    have key := cond_ratio G β σ τ v h
    have hZne : (∑ η : Vv → Bool, isingWeight G β η) ≠ 0 := ne_of_gt hZ
    have hab : isingWeight G β (Function.update σ v true)
        + isingWeight G β (Function.update σ v false) ≠ 0 :=
      ne_of_gt (add_pos (isingWeight_pos G β _) (isingWeight_pos G β _))
    simp only [isingDist]
    rw [← key]
    field_simp
  · rw [if_neg h, if_neg h]

private lemma pT_mem (σ : Vv → Bool) (v : Vv) : 0 ≤ pT G β σ v ∧ pT G β σ v ≤ 1 := by
  have h := abs_lt.mp (tanh_lt_one' (β * ((Sz G σ v : ℤ) : ℝ)))
  constructor <;> simp only [pT] <;> linarith [h.1, h.2]

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma isingZ_pos : (0 : ℝ) < ∑ η : Vv → Bool, isingWeight G β η :=
  Finset.sum_pos (fun η _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

private lemma isingDist_pos (σ : Vv → Bool) : 0 < isingDist G β σ := by
  rw [isingDist]
  exact div_pos (Real.exp_pos _) (isingZ_pos G β)

private lemma isingDist_isDist : IsDist (isingDist G β) := by
  refine ⟨fun σ => (isingDist_pos G β σ).le, ?_⟩
  simp only [isingDist]
  rw [← sum_div_const, div_self (ne_of_gt (isingZ_pos G β))]

private lemma glauber_stochastic [Nonempty Vv] : IsStochastic (glauber (isingDist G β)) := by
  have h := glauber_stationary (isingDist G β) (isingDist_isDist G β)
  exact ⟨h.1, fun x => h.2.1 x (isingDist_pos G β x)⟩

private lemma glauber_stat [Nonempty Vv] :
    IsStationary (glauber (isingDist G β)) (isingDist G β) :=
  (glauber_stationary (isingDist G β) (isingDist_isDist G β)).2.2.2


/-! ### The Glauber expectation operator -/

private lemma glauber_expect [Nonempty Vv] (σ : Vv → Bool) (f : (Vv → Bool) → ℝ) :
    ∑ τ : Vv → Bool, glauber (isingDist G β) σ τ * f τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, ∑ s : Bool,
          pB G β σ v s * f (Function.update σ v s) := by
  classical
  have h1 : ∀ τ : Vv → Bool, glauber (isingDist G β) σ τ * f τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv,
          (if ∀ w : Vv, w ≠ v → τ w = σ w then pB G β σ v (τ v) * f τ else 0) := by
    intro τ
    rw [glauber_apply, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hh : ∀ w : Vv, w ≠ v → τ w = σ w
    · rw [if_pos hh, if_pos hh]
    · rw [if_neg hh, if_neg hh, zero_mul]
  have hinner : ∀ v : Vv,
      (∑ τ : Vv → Bool,
        (if ∀ w : Vv, w ≠ v → τ w = σ w then pB G β σ v (τ v) * f τ else 0))
        = ∑ s : Bool, pB G β σ v s * f (Function.update σ v s) := by
    intro v
    rw [← Finset.sum_filter, filter_pair, Finset.sum_pair (update_ne σ v), Fintype.sum_bool]
    simp
  rw [Finset.sum_congr rfl fun τ _ => h1 τ, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun v _ => hinner v]

private lemma pB_add' (σ : Vv → Bool) (v : Vv) : ∑ s : Bool, pB G β σ v s = 1 := by
  rw [Fintype.sum_bool]
  exact pB_add G β σ v

/-- The magnetization. -/
private def magn (σ : Vv → Bool) : ℝ := ∑ v : Vv, spin σ v

private lemma magn_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    magn (Function.update σ v s) = magn σ - spin σ v + ((sgnZ s : ℤ) : ℝ) := by
  classical
  simp only [magn]
  rw [← Finset.add_sum_erase _ (fun w => spin (Function.update σ v s) w) (Finset.mem_univ v),
    ← Finset.add_sum_erase _ (fun w => spin σ w) (Finset.mem_univ v)]
  have herase : ∑ w ∈ univ.erase v, spin (Function.update σ v s) w
      = ∑ w ∈ univ.erase v, spin σ w :=
    Finset.sum_congr rfl fun w hw => spin_update_ne σ v s (Finset.ne_of_mem_erase hw)
  rw [herase, spin_update_self]
  ring

private lemma pB_diff (σ : Vv → Bool) (v : Vv) :
    pB G β σ v true - pB G β σ v false = Real.tanh (β * ((Sz G σ v : ℤ) : ℝ)) := by
  have h1 : pB G β σ v true = pT G β σ v := by simp [pB]
  have h2 : pB G β σ v false = 1 - pT G β σ v := by simp [pB]
  rw [h1, h2]
  simp only [pT]
  ring

private lemma magn_le (σ : Vv → Bool) : |magn σ| ≤ (Fintype.card Vv : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h : ∀ v : Vv, |spin σ v| ≤ 1 := by
    intro v
    cases hv : σ v <;> simp [spin, hv]
  refine le_trans (Finset.sum_le_sum fun v _ => h v) ?_
  simp [Finset.card_univ]

end Ising

/-! ### The cycle -/

section Cycle

variable {n : ℕ} [NeZero n]

private lemma zmod_one_ne_zero (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero

private lemma zmod_two_ne_zero (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  have := ZMod.val_cast_of_lt (n := n) (by omega : 2 < n)
  rw [h2, ZMod.val_zero] at this
  omega

private lemma cyc_neighborFinset (hn : 3 ≤ n) (v : ZMod n) :
    (cycleGraph n).neighborFinset v = {v + 1, v - 1} := by
  have h1 := zmod_one_ne_zero hn
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    rcases hy with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; ring)
  · intro hy
    rcases hy with h | h
    · refine ⟨?_, Or.inl h⟩
      rw [h]
      intro hc
      exact h1 (by linear_combination -hc)
    · refine ⟨?_, Or.inr (by rw [h]; ring)⟩
      rw [h]
      intro hc
      exact h1 (by linear_combination hc)

private lemma cyc_degree (hn : 3 ≤ n) (v : ZMod n) : (cycleGraph n).degree v = 2 := by
  have hdeg : (cycleGraph n).degree v = ((cycleGraph n).neighborFinset v).card := rfl
  rw [hdeg, cyc_neighborFinset hn v]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro hc
  exact zmod_two_ne_zero hn (by linear_combination hc)

private lemma cyc_maxDegree (hn : 3 ≤ n) : (cycleGraph n).maxDegree = 2 := by
  refine le_antisymm ?_ ?_
  · exact SimpleGraph.maxDegree_le_of_forall_degree_le _ 2 fun v => le_of_eq (cyc_degree hn v)
  · have := SimpleGraph.degree_le_maxDegree (cycleGraph n) (0 : ZMod n)
    rw [cyc_degree hn] at this
    exact this

private lemma cyc_Sz (hn : 3 ≤ n) (σ : ZMod n → Bool) (v : ZMod n) :
    Sz (cycleGraph n) σ v = sgnZ (σ (v + 1)) + sgnZ (σ (v - 1)) := by
  have hne : v + 1 ≠ v - 1 := by
    intro hc
    exact zmod_two_ne_zero hn (by linear_combination hc)
  simp only [Sz]
  rw [← Finset.sum_filter]
  have hfil : (univ.filter fun w : ZMod n => (cycleGraph n).Adj v w)
      = (cycleGraph n).neighborFinset v := by
    ext w; simp [SimpleGraph.mem_neighborFinset]
  rw [hfil, cyc_neighborFinset hn v, Finset.sum_pair hne]


private lemma cyc_tanh (hn : 3 ≤ n) (β : ℝ) (σ : ZMod n → Bool) (v : ZMod n) :
    Real.tanh (β * ((Sz (cycleGraph n) σ v : ℤ) : ℝ))
      = (Real.tanh (2 * β) / 2) * ((Sz (cycleGraph n) σ v : ℤ) : ℝ) := by
  rw [cyc_Sz hn]
  cases h1 : σ (v + 1) <;> cases h2 : σ (v - 1) <;>
    simp only [sgnZ, Bool.false_eq_true, if_false, if_true] <;> push_cast
  · rw [show β * (-2 : ℝ) = -(2 * β) from by ring, Real.tanh_neg]
    ring
  · rw [mul_zero, Real.tanh_zero]
    ring
  · rw [mul_zero, Real.tanh_zero]
    ring
  · rw [show β * (2 : ℝ) = 2 * β from by ring]
    ring

private lemma cyc_sum_Sz (hn : 3 ≤ n) (σ : ZMod n → Bool) :
    ∑ v : ZMod n, ((Sz (cycleGraph n) σ v : ℤ) : ℝ) = 2 * magn σ := by
  have h : ∀ v : ZMod n, ((Sz (cycleGraph n) σ v : ℤ) : ℝ)
      = spin σ (v + 1) + spin σ (v - 1) := by
    intro v
    rw [cyc_Sz hn]
    push_cast
    rw [← spin_eq, ← spin_eq]
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib]
  have e1 : ∑ v : ZMod n, spin σ (v + 1) = ∑ v : ZMod n, spin σ v :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun v => rfl)
  have e2 : ∑ v : ZMod n, spin σ (v - 1) = ∑ v : ZMod n, spin σ v :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod n)) _ _ (fun v => rfl)
  rw [e1, e2]
  show _ = 2 * ∑ v : ZMod n, spin σ v
  ring

private lemma magn_step (hn : 3 ≤ n) (β : ℝ) (σ : ZMod n → Bool) :
    ∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * magn τ
      = (1 - (1 - Real.tanh (2 * β)) / n) * magn σ := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hcard : (Fintype.card (ZMod n) : ℝ) = (n : ℝ) := by
    rw [ZMod.card]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [glauber_expect]
  have hinner : ∀ v : ZMod n,
      (∑ s : Bool, pB (cycleGraph n) β σ v s * magn (Function.update σ v s))
        = magn σ - spin σ v
          + (Real.tanh (2 * β) / 2) * ((Sz (cycleGraph n) σ v : ℤ) : ℝ) := by
    intro v
    rw [Fintype.sum_bool, magn_update, magn_update]
    have hadd := pB_add (cycleGraph n) β σ v
    have hdiff := pB_diff (cycleGraph n) β σ v
    have hct := cyc_tanh hn β σ v
    have hT : ((sgnZ true : ℤ) : ℝ) = 1 := by simp [sgnZ]
    have hF : ((sgnZ false : ℤ) : ℝ) = -1 := by simp [sgnZ]
    rw [hT, hF, ← hct]
    linear_combination (magn σ - spin σ v) * hadd + hdiff
  rw [Finset.sum_congr rfl fun v _ => hinner v, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, cyc_sum_Sz hn]
  have hsum1 : ∑ _v : ZMod n, magn σ = (n : ℝ) * magn σ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
  have hsum2 : ∑ v : ZMod n, spin σ v = magn σ := rfl
  rw [hsum1, hsum2, hcard]
  field_simp
  ring

private lemma magn_pow (hn : 3 ≤ n) (β : ℝ) (t : ℕ) (σ : ZMod n → Bool) :
    ∑ τ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ τ * magn τ
      = (1 - (1 - Real.tanh (2 * β)) / n) ^ t * magn σ := by
  induction t generalizing σ with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ σ magn]
    simp
  | succ t ih =>
    have hexp : ∀ τ : ZMod n → Bool,
        ((glauber (isingDist (cycleGraph n) β)) ^ (t + 1)) σ τ
          = ∑ ρ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ ρ
              * ((glauber (isingDist (cycleGraph n) β)) ^ t) ρ τ := by
      intro τ
      rw [pow_succ']
      exact Matrix.mul_apply
    calc ∑ τ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ (t + 1)) σ τ * magn τ
        = ∑ τ : ZMod n → Bool, ∑ ρ : ZMod n → Bool,
            glauber (isingDist (cycleGraph n) β) σ ρ
              * (((glauber (isingDist (cycleGraph n) β)) ^ t) ρ τ * magn τ) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [hexp τ, Finset.sum_mul]
          exact Finset.sum_congr rfl fun ρ _ => by ring
      _ = ∑ ρ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ ρ
            * ∑ τ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) ρ τ * magn τ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => (Finset.mul_sum _ _ _).symm
      _ = (1 - (1 - Real.tanh (2 * β)) / n) ^ t
            * ∑ ρ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ ρ * magn ρ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => by rw [ih ρ]; ring
      _ = (1 - (1 - Real.tanh (2 * β)) / n) ^ (t + 1) * magn σ := by
          rw [magn_step hn]
          ring

/-! ### Second moments -/

private lemma pow_nonneg_of_stochastic {W : Type*} [Fintype W] [DecidableEq W]
    {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (t : ℕ) (z p : W) : 0 ≤ (Q ^ t) z p := by
  induction t generalizing p with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z' _ => mul_nonneg (ih z') (hQ.1 _ _)

private lemma pow_row_sum {W : Type*} [Fintype W] [DecidableEq W]
    {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (t : ℕ) (x : W) : ∑ y : W, (Q ^ t) x y = 1 := by
  induction t generalizing x with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [Finset.sum_ite_eq Finset.univ x (fun _ => (1 : ℝ))]
    simp
  | succ t ih =>
    have h : ∀ y : W, (Q ^ (t + 1)) x y = ∑ z : W, Q x z * (Q ^ t) z y := by
      intro y; rw [pow_succ']; exact Matrix.mul_apply
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm]
    rw [Finset.sum_congr rfl fun z _ => by rw [ih z, mul_one]]
    exact hQ.2 x

private lemma distVar_eq {W : Type*} [Fintype W] [DecidableEq W] (μ : W → ℝ) (hμ : IsDist μ)
    (f : W → ℝ) : distVar μ f = (∑ x : W, (f x) ^ 2 * μ x) - (distExp μ f) ^ 2 := by
  simp only [distVar, distExp]
  have hexp : ∀ x : W, (f x - ∑ y : W, f y * μ y) ^ 2 * μ x
      = (f x) ^ 2 * μ x - 2 * (∑ y : W, f y * μ y) * (f x * μ x)
        + (∑ y : W, f y * μ y) ^ 2 * μ x := by
    intro x; ring
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hμ.2, mul_one]
  ring

/-- The one-step change of the magnetization is at most `2`. -/
private lemma magn_sq_step (hn : 3 ≤ n) (β : ℝ) (σ : ZMod n → Bool) :
    ∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * (magn τ - magn σ) ^ 2
      ≤ 4 := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [glauber_expect]
  have hbd : ∀ (v : ZMod n) (s : Bool),
      pB (cycleGraph n) β σ v s * (magn (Function.update σ v s) - magn σ) ^ 2
        ≤ pB (cycleGraph n) β σ v s * 4 := by
    intro v s
    refine mul_le_mul_of_nonneg_left ?_ (pB_nonneg (cycleGraph n) β σ v s)
    rw [magn_update]
    have h1 : |spin σ v| ≤ 1 := by cases hv : σ v <;> simp [spin, hv]
    have h2 : |((sgnZ s : ℤ) : ℝ)| ≤ 1 := by cases s <;> simp [sgnZ]
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp h2
    nlinarith [h3.1, h3.2, h4.1, h4.2]
  have hstep : ∀ v : ZMod n,
      (∑ s : Bool, pB (cycleGraph n) β σ v s * (magn (Function.update σ v s) - magn σ) ^ 2)
        ≤ 4 := by
    intro v
    refine le_trans (Finset.sum_le_sum fun s _ => hbd v s) ?_
    rw [← Finset.sum_mul, pB_add' (cycleGraph n) β σ v]
    norm_num
  have hsum : (∑ v : ZMod n, ∑ s : Bool,
      pB (cycleGraph n) β σ v s * (magn (Function.update σ v s) - magn σ) ^ 2)
        ≤ (n : ℝ) * 4 := by
    refine le_trans (Finset.sum_le_sum fun v _ => hstep v) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
  rw [ZMod.card]
  rw [inv_mul_eq_div, div_le_iff₀ hnpos]
  linarith

private lemma magn_sq_one_step (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) (σ : ZMod n → Bool) :
    ∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * (magn τ) ^ 2
      ≤ 4 + (1 - (1 - Real.tanh (2 * β)) / n) ^ 2 * (magn σ) ^ 2 := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hP := glauber_stochastic (cycleGraph n) β
  have hexp : ∀ τ : ZMod n → Bool,
      glauber (isingDist (cycleGraph n) β) σ τ * (magn τ) ^ 2
        = glauber (isingDist (cycleGraph n) β) σ τ * (magn τ - magn σ) ^ 2
          + 2 * magn σ * (glauber (isingDist (cycleGraph n) β) σ τ * magn τ)
          - 2 * (magn σ) ^ 2 * glauber (isingDist (cycleGraph n) β) σ τ
          + (magn σ) ^ 2 * glauber (isingDist (cycleGraph n) β) σ τ := by
    intro τ; ring
  rw [Finset.sum_congr rfl fun τ _ => hexp τ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, magn_step hn, hP.2 σ]
  have h1 := magn_sq_step hn β σ
  have hsq : (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ 2
      ≥ 2 * (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) - 1 := by
    nlinarith [sq_nonneg ((1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) - 1)]
  nlinarith [h1, hsq, sq_nonneg (magn σ)]

private lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h1 : 0 ≤ Real.sinh x := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr hx
  positivity

private lemma lam_lt_one (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) :
    0 < 1 - (1 - Real.tanh (2 * β)) / (n : ℝ)
      ∧ 1 - (1 - Real.tanh (2 * β)) / (n : ℝ) < 1 := by
  have hnpos : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.tanh (2 * β) < 1 := (abs_lt.mp (tanh_lt_one' (2 * β))).2
  have h2 : 0 ≤ Real.tanh (2 * β) := tanh_nonneg (by linarith)
  have h3 : 0 < (1 - Real.tanh (2 * β)) / (n : ℝ) := by
    apply div_pos (by linarith) (by linarith)
  have h4 : (1 - Real.tanh (2 * β)) / (n : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact ⟨by linarith, by linarith⟩

private lemma M2_bound (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) (σ : ZMod n → Bool) (t : ℕ) :
    ∑ τ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ τ * (magn τ) ^ 2
      ≤ (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ (2 * t) * (magn σ) ^ 2
        + 4 / (1 - (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ 2) := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hP := glauber_stochastic (cycleGraph n) β
  obtain ⟨hl0, hl1⟩ := lam_lt_one hn β hβ
  set lam : ℝ := 1 - (1 - Real.tanh (2 * β)) / (n : ℝ) with hlam
  have hden : 0 < 1 - lam ^ 2 := by nlinarith
  have hB : 4 + lam ^ 2 * (4 / (1 - lam ^ 2)) = 4 / (1 - lam ^ 2) := by
    field_simp
    ring
  have hBnn : 0 ≤ 4 / (1 - lam ^ 2) := by positivity
  induction t with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, Nat.mul_zero]
    rw [Finset.sum_ite_eq Finset.univ σ (fun τ => (magn τ) ^ 2)]
    simp only [Finset.mem_univ, if_true, pow_zero, one_mul]
    linarith
  | succ t ih =>
    have hexp : ∀ τ : ZMod n → Bool,
        ((glauber (isingDist (cycleGraph n) β)) ^ (t + 1)) σ τ
          = ∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ
              * glauber (isingDist (cycleGraph n) β) ρ τ := by
      intro τ
      rw [pow_succ]
      exact Matrix.mul_apply
    have hstep : ∑ τ : ZMod n → Bool,
        ((glauber (isingDist (cycleGraph n) β)) ^ (t + 1)) σ τ * (magn τ) ^ 2
        = ∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ
            * (∑ τ : ZMod n → Bool,
                glauber (isingDist (cycleGraph n) β) ρ τ * (magn τ) ^ 2) := by
      rw [Finset.sum_congr rfl fun τ _ => by rw [hexp τ, Finset.sum_mul], Finset.sum_comm]
      exact Finset.sum_congr rfl fun ρ _ =>
        by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hstep]
    have hle : ∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ
          * (∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) ρ τ * (magn τ) ^ 2)
        ≤ ∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ
            * (4 + lam ^ 2 * (magn ρ) ^ 2) :=
      Finset.sum_le_sum fun ρ _ =>
        mul_le_mul_of_nonneg_left (magn_sq_one_step hn β hβ ρ)
          (pow_nonneg_of_stochastic hP t σ ρ)
    refine le_trans hle ?_
    have hsplit : ∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ
          * (4 + lam ^ 2 * (magn ρ) ^ 2)
        = 4 * (∑ ρ : ZMod n → Bool, ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ)
          + lam ^ 2 * (∑ ρ : ZMod n → Bool,
              ((glauber (isingDist (cycleGraph n) β)) ^ t) σ ρ * (magn ρ) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [hsplit, pow_row_sum hP]
    have hpow : lam ^ (2 * (t + 1)) = lam ^ 2 * lam ^ (2 * t) := by ring
    have hl2 : (0 : ℝ) ≤ lam ^ 2 := sq_nonneg lam
    nlinarith [ih, hB, hpow]

private lemma stat_M2 (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) :
    ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ * (magn σ) ^ 2
      ≤ 4 / (1 - (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ 2) := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  obtain ⟨hl0, hl1⟩ := lam_lt_one hn β hβ
  set lam : ℝ := 1 - (1 - Real.tanh (2 * β)) / (n : ℝ) with hlam
  have hden : 0 < 1 - lam ^ 2 := by nlinarith
  have hpi := glauber_stat (cycleGraph n) β
  have hpid := isingDist_isDist (cycleGraph n) β
  set E : ℝ := ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ * (magn σ) ^ 2 with hE
  have hkey : E ≤ 4 + lam ^ 2 * E := by
    have hstat : ∀ τ : ZMod n → Bool,
        ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
          * glauber (isingDist (cycleGraph n) β) σ τ = isingDist (cycleGraph n) β τ := by
      intro τ
      have := congrFun hpi.2 τ
      simpa [Matrix.vecMul, dotProduct] using this
    have h1 : E = ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
        * (∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * (magn τ) ^ 2) := by
      rw [hE]
      rw [Finset.sum_congr rfl fun τ _ => by rw [← hstat τ, Finset.sum_mul]]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ =>
        by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
    have h2 : ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
          * (∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * (magn τ) ^ 2)
        ≤ ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ * (4 + lam ^ 2 * (magn σ) ^ 2) :=
      Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_left (magn_sq_one_step hn β hβ σ) (hpid.1 σ)
    have h3 : ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
          * (4 + lam ^ 2 * (magn σ) ^ 2) = 4 + lam ^ 2 * E := by
      have hd : ∀ σ : ZMod n → Bool,
          isingDist (cycleGraph n) β σ * (4 + lam ^ 2 * (magn σ) ^ 2)
            = 4 * isingDist (cycleGraph n) β σ
              + lam ^ 2 * (isingDist (cycleGraph n) β σ * (magn σ) ^ 2) := fun σ => by ring
      rw [Finset.sum_congr rfl fun σ _ => hd σ, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hpid.2, mul_one, ← hE]
    calc E = ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
          * (∑ τ : ZMod n → Bool, glauber (isingDist (cycleGraph n) β) σ τ * (magn τ) ^ 2) := h1
      _ ≤ ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ
            * (4 + lam ^ 2 * (magn σ) ^ 2) := h2
      _ = 4 + lam ^ 2 * E := h3
  rw [le_div_iff₀ hden]
  nlinarith [hkey]

/-! ### The spin-flip symmetry -/

private lemma spin_flip {Vv : Type*} [Fintype Vv] [DecidableEq Vv] (σ : Vv → Bool) (v : Vv) :
    spin (fun w => !(σ w)) v = -spin σ v := by
  cases h : σ v <;> simp [spin, h]

private lemma isingWeight_flip {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) :
    isingWeight G β (fun w => !(σ w)) = isingWeight G β σ := by
  have hsum : (∑ u : Vv, ∑ w : Vv, if G.Adj u w then
        spin (fun z => !(σ z)) u * spin (fun z => !(σ z)) w else 0)
      = ∑ u : Vv, ∑ w : Vv, if G.Adj u w then spin σ u * spin σ w else 0 := by
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj u w
    · rw [if_pos h, if_pos h, spin_flip, spin_flip]; ring
    · rw [if_neg h, if_neg h]
  simp only [isingWeight]
  rw [hsum]

private lemma isingDist_flip {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) :
    isingDist G β (fun w => !(σ w)) = isingDist G β σ := by
  simp only [isingDist, isingWeight_flip]

private lemma magn_flip {Vv : Type*} [Fintype Vv] [DecidableEq Vv] (σ : Vv → Bool) :
    magn (fun w => !(σ w)) = -magn σ := by
  simp only [magn]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun v _ => spin_flip σ v

private lemma stat_magn_zero {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    distExp (isingDist G β) (magn : (Vv → Bool) → ℝ) = 0 := by
  have hinv : Function.Involutive (fun σ : Vv → Bool => fun w => !(σ w)) := by
    intro σ
    funext w
    simp
  have hcomp := Equiv.sum_comp (hinv.toPerm _)
    (fun σ : Vv → Bool => magn σ * isingDist G β σ)
  have hval : ∀ σ : Vv → Bool,
      magn ((hinv.toPerm _) σ) * isingDist G β ((hinv.toPerm _) σ)
        = -(magn σ * isingDist G β σ) := by
    intro σ
    show magn (fun w => !(σ w)) * isingDist G β (fun w => !(σ w)) = _
    rw [magn_flip, isingDist_flip]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hval σ, Finset.sum_neg_distrib] at hcomp
  simp only [distExp]
  linarith [hcomp]

/-! ### The lower bound -/

private lemma dist_lower (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) (t : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hcond : 4 * ε / (1 - ε)
      < (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ (2 * t) * (n : ℝ)
          * (1 - Real.tanh (2 * β)) / 4) :
    ε < distStationary (glauber (isingDist (cycleGraph n) β))
        (isingDist (cycleGraph n) β) t := by
  classical
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hP := glauber_stochastic (cycleGraph n) β
  have hpid := isingDist_isDist (cycleGraph n) β
  have hN : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hc0 : 0 < 1 - Real.tanh (2 * β) := by
    have := (abs_lt.mp (tanh_lt_one' (2 * β))).2
    linarith
  obtain ⟨hl0, hl1⟩ := lam_lt_one hn β hβ
  set lam : ℝ := 1 - (1 - Real.tanh (2 * β)) / (n : ℝ) with hlam
  have hden : 0 < 1 - lam ^ 2 := by nlinarith
  set B : ℝ := 4 / (1 - lam ^ 2) with hBdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  set σ₀ : ZMod n → Bool := fun _ => true with hσ0
  have hm0 : magn σ₀ = (n : ℝ) := by
    simp only [magn, hσ0, spin, if_true]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  set μ : (ZMod n → Bool) → ℝ :=
    rowDist (glauber (isingDist (cycleGraph n) β)) t σ₀ with hμdef
  have hμd : IsDist μ :=
    ⟨fun τ => pow_nonneg_of_stochastic hP t σ₀ τ, pow_row_sum hP t σ₀⟩
  have hEμ : distExp μ magn = lam ^ t * (n : ℝ) := by
    simp only [distExp, hμdef, rowDist]
    rw [Finset.sum_congr rfl fun τ _ => mul_comm (magn τ)
      (((glauber (isingDist (cycleGraph n) β)) ^ t) σ₀ τ), magn_pow hn β t σ₀, hm0]
  have hEπ : distExp (isingDist (cycleGraph n) β) (magn : (ZMod n → Bool) → ℝ) = 0 :=
    stat_magn_zero (cycleGraph n) β
  have hVμ : distVar μ magn ≤ B := by
    rw [distVar_eq μ hμd magn, hEμ]
    have hm := M2_bound hn β hβ σ₀ t
    rw [hm0] at hm
    have heq : ∑ τ : ZMod n → Bool, (magn τ) ^ 2 * μ τ
        = ∑ τ : ZMod n → Bool,
            ((glauber (isingDist (cycleGraph n) β)) ^ t) σ₀ τ * (magn τ) ^ 2 :=
      Finset.sum_congr rfl fun τ _ => mul_comm _ _
    rw [heq]
    have hpow2 : lam ^ (2 * t) = (lam ^ t) ^ 2 := by
      rw [pow_mul']
    rw [hpow2] at hm
    nlinarith [hm]
  have hVπ : distVar (isingDist (cycleGraph n) β) (magn : (ZMod n → Bool) → ℝ) ≤ B := by
    rw [distVar_eq _ hpid magn, hEπ]
    have hm := stat_M2 hn β hβ
    have heq : ∑ σ : ZMod n → Bool, (magn σ) ^ 2 * isingDist (cycleGraph n) β σ
        = ∑ σ : ZMod n → Bool, isingDist (cycleGraph n) β σ * (magn σ) ^ 2 :=
      Finset.sum_congr rfl fun σ _ => mul_comm _ _
    rw [heq]
    linarith [hm]
  -- the distinguishing statistic
  have hlt0 : 0 < lam ^ t := pow_pos hl0 t
  have hnum : 0 < lam ^ t * (n : ℝ) := by positivity
  set r : ℝ := lam ^ t * (n : ℝ) / Real.sqrt B with hrdef
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hsep : r * Real.sqrt ((distVar μ magn
      + distVar (isingDist (cycleGraph n) β) magn) / 2)
      ≤ |distExp μ magn - distExp (isingDist (cycleGraph n) β) magn| := by
    rw [hEμ, hEπ, sub_zero, abs_of_pos hnum]
    have h1 : (distVar μ magn + distVar (isingDist (cycleGraph n) β) magn) / 2 ≤ B := by
      linarith
    have h2 : Real.sqrt ((distVar μ magn
        + distVar (isingDist (cycleGraph n) β) magn) / 2) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt h1
    calc r * Real.sqrt ((distVar μ magn
          + distVar (isingDist (cycleGraph n) β) magn) / 2)
        ≤ r * Real.sqrt B := mul_le_mul_of_nonneg_left h2 hr0
      _ = lam ^ t * (n : ℝ) := by
          rw [hrdef, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hsB), mul_one]
  have hmean : distExp μ magn ≠ distExp (isingDist (cycleGraph n) β) magn := by
    rw [hEμ, hEπ]
    exact ne_of_gt hnum
  have hds := distinguishing_statistic_nondegenerate μ (isingDist (cycleGraph n) β)
    hμd hpid magn hmean r hr0 hsep
  have hr2 : r ^ 2 = (lam ^ t * (n : ℝ)) ^ 2 / B := by
    rw [hrdef, div_pow, Real.sq_sqrt hB0.le]
  -- compare with the given condition
  have hRle : (lam ^ (2 * t) * (n : ℝ) * (1 - Real.tanh (2 * β)) / 4) ≤ r ^ 2 := by
    rw [hr2, hBdef]
    have hexp : (lam ^ t * (n : ℝ)) ^ 2 = lam ^ (2 * t) * (n : ℝ) ^ 2 := by
      rw [pow_mul']
      ring
    rw [hexp, div_div_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    have h1 : (1 - Real.tanh (2 * β)) / (n : ℝ) ≤ 1 - lam ^ 2 := by
      rw [hlam]
      nlinarith
    have h2 : 0 ≤ lam ^ (2 * t) := by positivity
    have h3 : lam ^ (2 * t) * (n : ℝ) ^ 2 * ((1 - Real.tanh (2 * β)) / (n : ℝ))
        = lam ^ (2 * t) * (n : ℝ) * (1 - Real.tanh (2 * β)) := by
      field_simp
      try ring
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (sq_nonneg (n : ℝ)))]
  have harith : ε < 1 - 4 / (4 + r ^ 2) := by
    have hR := lt_of_lt_of_le hcond hRle
    have h4 : (0 : ℝ) < 4 + r ^ 2 := by positivity
    have he : (0 : ℝ) < 1 - ε := by linarith
    rw [div_lt_iff₀ he] at hR
    have key : 4 / (4 + r ^ 2) < 1 - ε := by
      rw [div_lt_iff₀ h4]
      nlinarith [hR]
    linarith
  have hfin : tvDist μ (isingDist (cycleGraph n) β)
      ≤ distStationary (glauber (isingDist (cycleGraph n) β))
        (isingDist (cycleGraph n) β) t := by
    simp only [distStationary]
    exact le_ciSup (f := fun x : ZMod n → Bool =>
      tvDist (rowDist (glauber (isingDist (cycleGraph n) β)) t x)
        (isingDist (cycleGraph n) β)) (Finite.bddAbove_range _) σ₀
  linarith [hds, hfin, harith]

/-! ### Irreducibility and aperiodicity of the Glauber chain -/

private lemma pB_pos {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) (v : Vv) (s : Bool) :
    0 < pB G β σ v s := by
  have h := abs_lt.mp (tanh_lt_one' (β * ((Sz G σ v : ℤ) : ℝ)))
  cases s <;>
    simp only [pB, pT, if_true, if_false, Bool.false_eq_true] <;> linarith [h.1, h.2]

private lemma glauber_self_pos {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) :
    0 < glauber (isingDist G β) σ σ := by
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [glauber_apply]
  refine mul_pos (by positivity) (Finset.sum_pos (fun v _ => ?_) ⟨Classical.arbitrary Vv,
    Finset.mem_univ _⟩)
  rw [if_pos (fun w _ => rfl)]
  exact pB_pos G β σ v (σ v)

private lemma glauber_update_pos {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) (v : Vv) (s : Bool) :
    0 < glauber (isingDist G β) σ (Function.update σ v s) := by
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [glauber_apply]
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos' (fun w _ => ?_) ⟨v, Finset.mem_univ v, ?_⟩
  · split_ifs
    · exact (pB_pos G β σ w _).le
    · exact le_refl 0
  · rw [if_pos (fun w hw => by rw [Function.update_apply, if_neg hw])]
    rw [Function.update_self]
    exact pB_pos G β σ v s

private lemma diffSet_update_self {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    (σ τ : Vv → Bool) (v : Vv) :
    diffSet (Function.update σ v (τ v)) τ = (diffSet σ τ).erase v := by
  ext w
  simp only [mem_diffSet, Finset.mem_erase]
  by_cases hw : w = v
  · subst hw
    simp
  · rw [Function.update_apply, if_neg hw]
    simp [hw, mem_diffSet]

private lemma diffSet_empty_eq {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    {σ τ : Vv → Bool} (h : diffSet σ τ = ∅) : σ = τ := by
  funext v
  by_contra hc
  have hv : v ∈ diffSet σ τ := (mem_diffSet σ τ v).mpr hc
  rw [h] at hv
  exact absurd hv (Finset.notMem_empty v)

private lemma pow_pos_of_diff {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    ∀ (k : ℕ) (σ τ : Vv → Bool), (diffSet σ τ).card ≤ k
      → 0 < ((glauber (isingDist G β)) ^ k) σ τ := by
  have hP := glauber_stochastic G β
  intro k
  induction k with
  | zero =>
    intro σ τ h
    have hst : σ = τ := diffSet_empty_eq (Finset.card_eq_zero.mp (by omega))
    subst hst
    rw [pow_zero, Matrix.one_apply_eq]
    norm_num
  | succ k ih =>
    intro σ τ h
    have hlow : ∀ ρ : Vv → Bool,
        glauber (isingDist G β) σ ρ * ((glauber (isingDist G β)) ^ k) ρ τ
          ≤ ((glauber (isingDist G β)) ^ (k + 1)) σ τ := by
      intro ρ
      have hexp : ((glauber (isingDist G β)) ^ (k + 1)) σ τ
          = ∑ ρ' : Vv → Bool, glauber (isingDist G β) σ ρ'
              * ((glauber (isingDist G β)) ^ k) ρ' τ := by
        rw [pow_succ']
        exact Matrix.mul_apply
      rw [hexp]
      exact Finset.single_le_sum
        (f := fun ρ' : Vv → Bool => glauber (isingDist G β) σ ρ'
          * ((glauber (isingDist G β)) ^ k) ρ' τ)
        (fun ρ' _ => mul_nonneg (hP.1 _ _) (pow_nonneg_of_stochastic hP k ρ' τ))
        (Finset.mem_univ ρ)
    by_cases hd : (diffSet σ τ).Nonempty
    · obtain ⟨v, hvmem⟩ := hd
      have hcard : (diffSet (Function.update σ v (τ v)) τ).card ≤ k := by
        rw [diffSet_update_self]
        have := Finset.card_erase_add_one hvmem
        omega
      refine lt_of_lt_of_le ?_ (hlow (Function.update σ v (τ v)))
      exact mul_pos (glauber_update_pos G β σ v (τ v)) (ih _ τ hcard)
    · have hst : σ = τ := diffSet_empty_eq (Finset.not_nonempty_iff_eq_empty.mp hd)
      subst hst
      refine lt_of_lt_of_le ?_ (hlow σ)
      refine mul_pos (glauber_self_pos G β σ) (ih σ σ ?_)
      have : diffSet σ σ = ∅ := by
        ext w
        simp [mem_diffSet]
      rw [this]
      simp

private lemma glauber_irreducible {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    Irreducible (glauber (isingDist G β)) :=
  fun σ τ => ⟨(diffSet σ τ).card, pow_pos_of_diff G β _ σ τ (le_refl _)⟩

private lemma glauber_aperiodic {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    Aperiodic (glauber (isingDist G β)) := by
  intro x
  have h1 : (1 : ℕ) ∈ returnSet (glauber (isingDist G β)) x := by
    refine ⟨le_refl 1, ?_⟩
    rw [pow_one]
    exact glauber_self_pos G β x
  have hset : {d : ℕ | ∀ t ∈ returnSet (glauber (isingDist G β)) x, d ∣ t} = {1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Nat.dvd_one.mp (h 1 h1)
    · intro h t _
      rw [h]
      exact one_dvd t
  rw [period, hset, csSup_singleton]

private lemma exists_mix {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, distStationary (glauber (isingDist G β)) (isingDist G β) t ≤ ε := by
  obtain ⟨α, ⟨hα0, hα1⟩, C, hC, hbd⟩ := convergence_theorem (glauber (isingDist G β))
    (glauber_stochastic G β) (glauber_irreducible G β) (glauber_aperiodic G β)
    (isingDist G β) (glauber_stat G β)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < ε / C by positivity) hα1
  refine ⟨t, le_trans (hbd t) ?_⟩
  calc C * α ^ t ≤ C * (ε / C) := mul_le_mul_of_nonneg_left ht.le hC.le
    _ = ε := by field_simp

/-! ### Assembling the two bounds -/

private lemma cyc_lower (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (T : ℕ)
    (hT : 4 * ε / (1 - ε)
      < (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ (2 * T) * (n : ℝ)
          * (1 - Real.tanh (2 * β)) / 4) :
    T ≤ mixingTime (glauber (isingDist (cycleGraph n) β)) (isingDist (cycleGraph n) β) ε := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  obtain ⟨hl0, hl1⟩ := lam_lt_one hn β hβ
  obtain ⟨t0, ht0⟩ := exists_mix (cycleGraph n) β ε hε
  have hne : {u : ℕ | distStationary (glauber (isingDist (cycleGraph n) β))
      (isingDist (cycleGraph n) β) u ≤ ε}.Nonempty := ⟨t0, ht0⟩
  have hmem : distStationary (glauber (isingDist (cycleGraph n) β))
      (isingDist (cycleGraph n) β)
      (mixingTime (glauber (isingDist (cycleGraph n) β))
        (isingDist (cycleGraph n) β) ε) ≤ ε := Nat.sInf_mem hne
  by_contra hcon
  push_neg at hcon
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hc0 : 0 < 1 - Real.tanh (2 * β) := by
    have := (abs_lt.mp (tanh_lt_one' (2 * β))).2
    linarith
  have hcondu : 4 * ε / (1 - ε)
      < (1 - (1 - Real.tanh (2 * β)) / (n : ℝ))
          ^ (2 * mixingTime (glauber (isingDist (cycleGraph n) β))
              (isingDist (cycleGraph n) β) ε)
        * (n : ℝ) * (1 - Real.tanh (2 * β)) / 4 := by
    have hmono : (1 - (1 - Real.tanh (2 * β)) / (n : ℝ)) ^ (2 * T)
        ≤ (1 - (1 - Real.tanh (2 * β)) / (n : ℝ))
            ^ (2 * mixingTime (glauber (isingDist (cycleGraph n) β))
                (isingDist (cycleGraph n) β) ε) :=
      pow_le_pow_of_le_one hl0.le hl1.le (by omega)
    have hfac : (0 : ℝ) ≤ (n : ℝ) * (1 - Real.tanh (2 * β)) / 4 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmono hfac
    have e1 : ∀ a : ℝ, a * ((n : ℝ) * (1 - Real.tanh (2 * β)) / 4)
        = a * (n : ℝ) * (1 - Real.tanh (2 * β)) / 4 := fun a => by ring
    rw [e1, e1] at hstep
    linarith
  have hlow := dist_lower hn β hβ _ ε hε hε1 hcondu
  linarith

private lemma cyc_upper (hn : 3 ≤ n) (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime (glauber (isingDist (cycleGraph n) β)) (isingDist (cycleGraph n) β) ε : ℝ)
      ≤ (n : ℝ) * (Real.log n + Real.log (1 / ε)) / (1 - Real.tanh (2 * β)) + 1 := by
  haveI : Nonempty (ZMod n) := ⟨0⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hc0 : 0 < 1 - Real.tanh (2 * β) := by
    have := (abs_lt.mp (tanh_lt_one' (2 * β))).2
    linarith
  have hEven : ∀ v : ZMod n, Even ((cycleGraph n).degree v) := by
    intro v
    rw [cyc_degree hn]
    exact ⟨1, rfl⟩
  have hmd : ((cycleGraph n).maxDegree : ℝ) = 2 := by
    rw [cyc_maxDegree hn]
    norm_num
  have hDob : ((cycleGraph n).maxDegree : ℝ) / 2 * Real.tanh (2 * β) < 1 := by
    rw [hmd]
    linarith
  have hmain := (ising_high_temperature (cycleGraph n) β hβ ε hε hε1).2 hEven hDob
  rw [hmd, ZMod.card] at hmain
  rw [show (1 : ℝ) - 2 / 2 * Real.tanh (2 * β) = 1 - Real.tanh (2 * β) from by ring] at hmain
  refine hmain.trans (le_of_lt (Nat.ceil_lt_add_one ?_))
  have h1 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have h2 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  positivity

end Cycle

end

end MarkovMixing

open MarkovMixing

open scoped BigOperators

set_option maxHeartbeats 2000000 in
/-- **Theorem 15.4** (LPW): the Glauber dynamics of the Ising model on the
`n`-cycle mixes in `n log n / c_O(β)` up to a factor `2`. -/
theorem solution (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ inst : NeZero n,
      (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) ≤
        (1 + δ) * n * Real.log n / (1 - Real.tanh (2 * β)) ∧
      (1 - δ) * n * Real.log n / (2 * (1 - Real.tanh (2 * β))) ≤
        (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) := by
  have hc0 : 0 < 1 - Real.tanh (2 * β) := by
    have := (abs_lt.mp (tanh_lt_one' (2 * β))).2
    linarith
  have hc1 : 1 - Real.tanh (2 * β) ≤ 1 := by
    have := tanh_nonneg (show (0:ℝ) ≤ 2 * β by linarith)
    linarith
  have hε0' : (0 : ℝ) < 1 - ε := by linarith
  set c : ℝ := 1 - Real.tanh (2 * β) with hcdef
  set K : ℝ := 16 * ε / ((1 - ε) * c) with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  set A : ℝ := (Real.log (1 / ε) + 1) / δ with hAdef
  set Bc : ℝ := 2 * (Real.log K + 1) / δ + 1 with hBcdef
  refine ⟨max (max 3 (⌈2 / δ⌉₊ + 1)) (max (⌈Real.exp A⌉₊ + 1) (⌈Real.exp Bc⌉₊ + 1)), ?_⟩
  intro n hnN inst
  haveI := inst
  have hn3 : 3 ≤ n := le_trans (le_trans (le_max_left 3 _) (le_max_left _ _)) hnN
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogeps : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  -- the three numerical consequences of `n ≥ N`
  have hstep1 : (⌈2 / δ⌉₊ + 1 : ℕ) ≤ n :=
    le_trans (le_trans (le_max_right 3 _) (le_max_left _ _)) hnN
  have hstep2 : (⌈Real.exp A⌉₊ + 1 : ℕ) ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hstep3 : (⌈Real.exp Bc⌉₊ + 1 : ℕ) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
  have hdelta : 2 / δ + 1 ≤ (n : ℝ) := by
    have h1 : (2 : ℝ) / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hstep1
    push_cast at h2
    linarith
  have hlogA : A < Real.log (n : ℝ) := by
    have h1 : Real.exp A ≤ (⌈Real.exp A⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp A⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hstep2
    push_cast at h2
    have h3 : Real.exp A < (n : ℝ) := by linarith
    have := Real.log_lt_log (Real.exp_pos A) h3
    rwa [Real.log_exp] at this
  have hlogB : Bc < Real.log (n : ℝ) := by
    have h1 : Real.exp Bc ≤ (⌈Real.exp Bc⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp Bc⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hstep3
    push_cast at h2
    have h3 : Real.exp Bc < (n : ℝ) := by linarith
    have := Real.log_lt_log (Real.exp_pos Bc) h3
    rwa [Real.log_exp] at this
  constructor
  · -- upper bound
    refine (cyc_upper hn3 β hβ ε hε hε1).trans ?_
    rw [← hcdef]
    have hkey : (n : ℝ) * Real.log (1 / ε) + c ≤ δ * ((n : ℝ) * Real.log (n : ℝ)) := by
      have h1 : Real.log (1 / ε) + 1 < δ * Real.log (n : ℝ) := by
        rw [hAdef, div_lt_iff₀ hδ] at hlogA
        linarith
      have h2 : (n : ℝ) * (Real.log (1 / ε) + 1) ≤ (n : ℝ) * (δ * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h1.le hnpos.le
      nlinarith [hn1, hc1]
    rw [div_add' _ _ _ (ne_of_gt hc0), div_le_div_iff₀ hc0 hc0]
    nlinarith [hkey]
  · -- lower bound
    rcases le_total 1 δ with hδ1 | hδ1
    · have hnn : (1 - δ) * (n : ℝ) * Real.log (n : ℝ) ≤ 0 := by
        have h1 : (0 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hnpos.le hL0
        have h2 : (0 : ℝ) ≤ δ - 1 := by linarith
        nlinarith [mul_nonneg h2 h1]
      have hpos : (0 : ℝ) < 2 * c := by linarith
      have : (1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnn hpos.le
      have hmix : (0 : ℝ) ≤ (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) := Nat.cast_nonneg _
      linarith
    · -- the interesting case `δ < 1`
      set lam : ℝ := 1 - c / (n : ℝ) with hlamdef
      obtain ⟨hl0, hl1⟩ := lam_lt_one hn3 β hβ
      rw [← hcdef, ← hlamdef] at hl0 hl1
      set T : ℕ := ⌈(1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c)⌉₊ with hTdef
      have hX0 : 0 ≤ (1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) := by
        have : (0 : ℝ) ≤ 1 - δ := by linarith
        positivity
      have hTX : (1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) ≤ (T : ℝ) := Nat.le_ceil _
      have hTlt : (T : ℝ) < (1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) + 1 :=
        Nat.ceil_lt_add_one hX0
      -- the logarithmic estimate
      have hnc : 0 < (n : ℝ) - c := by linarith
      have hloglam : -(c / ((n : ℝ) - c)) ≤ Real.log lam := by
        have hinv : Real.log (lam⁻¹) ≤ lam⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_inv] at hinv
        have hlv : lam⁻¹ - 1 = c / ((n : ℝ) - c) := by
          rw [hlamdef]
          field_simp
          ring
        rw [hlv] at hinv
        linarith
      have hTbound : 2 * (T : ℝ) * (c / ((n : ℝ) - c))
          ≤ (1 - δ / 2) * Real.log (n : ℝ) + 1 := by
        have hdelta' : 2 + δ ≤ δ * (n : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hdelta hδ.le
          have he : δ * (2 / δ + 1) = 2 + δ := by field_simp
          linarith [h, he.le, he.ge]
        have hratio : (n : ℝ) / ((n : ℝ) - c) ≤ 1 + δ / 2 := by
          rw [div_le_iff₀ hnc]
          nlinarith [hdelta', hc1, hc0, hδ.le,
            mul_nonneg (sub_nonneg.mpr hc1) (by linarith : (0 : ℝ) ≤ 1 + δ / 2)]
        have h2c : 2 * c / ((n : ℝ) - c) ≤ 1 := by
          rw [div_le_one hnc]
          linarith
        have hexp : 2 * (T : ℝ) * (c / ((n : ℝ) - c))
            ≤ 2 * ((1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) + 1) * (c / ((n : ℝ) - c)) := by
          have hcc : (0 : ℝ) ≤ c / ((n : ℝ) - c) := by positivity
          nlinarith [hTlt, hcc]
        have hcalc : 2 * ((1 - δ) * (n : ℝ) * Real.log (n : ℝ) / (2 * c) + 1)
            * (c / ((n : ℝ) - c))
            = (1 - δ) * Real.log (n : ℝ) * ((n : ℝ) / ((n : ℝ) - c)) + 2 * c / ((n : ℝ) - c) := by
          field_simp
          try ring
        rw [hcalc] at hexp
        have hb1 : (1 - δ) * Real.log (n : ℝ) * ((n : ℝ) / ((n : ℝ) - c))
            ≤ (1 - δ) * Real.log (n : ℝ) * (1 + δ / 2) := by
          have : (0 : ℝ) ≤ (1 - δ) * Real.log (n : ℝ) := by
            have : (0 : ℝ) ≤ 1 - δ := by linarith
            positivity
          exact mul_le_mul_of_nonneg_left hratio this
        have hb2 : (1 - δ) * Real.log (n : ℝ) * (1 + δ / 2)
            ≤ (1 - δ / 2) * Real.log (n : ℝ) := by
          nlinarith [mul_nonneg hL0 (mul_nonneg hδ.le hδ.le)]
        linarith
      have hpow : Real.exp (-((1 - δ / 2) * Real.log (n : ℝ) + 1)) ≤ lam ^ (2 * T) := by
        have hlam_exp : lam ^ (2 * T) = Real.exp ((2 * (T : ℝ)) * Real.log lam) := by
          have h1 : ((2 * T : ℕ) : ℝ) = 2 * (T : ℝ) := by push_cast; ring
          rw [← h1, Real.exp_nat_mul, Real.exp_log hl0]
        rw [hlam_exp]
        refine Real.exp_le_exp.mpr ?_
        have h1 : (2 * (T : ℝ)) * (-(c / ((n : ℝ) - c))) ≤ (2 * (T : ℝ)) * Real.log lam :=
          mul_le_mul_of_nonneg_left hloglam (by positivity)
        have h2 : -((1 - δ / 2) * Real.log (n : ℝ) + 1)
            ≤ (2 * (T : ℝ)) * (-(c / ((n : ℝ) - c))) := by
          have : 2 * (T : ℝ) * (c / ((n : ℝ) - c)) ≤ (1 - δ / 2) * Real.log (n : ℝ) + 1 :=
            hTbound
          linarith only [this]
        linarith
      have hcond : 4 * ε / (1 - ε) < lam ^ (2 * T) * (n : ℝ) * c / 4 := by
        have hK : Real.log K < δ / 2 * Real.log (n : ℝ) - 1 := by
          rw [hBcdef, div_add' _ _ _ (ne_of_gt hδ), div_lt_iff₀ hδ] at hlogB
          linarith
        have hKexp : K < Real.exp (δ / 2 * Real.log (n : ℝ) - 1) := by
          have := Real.exp_lt_exp.mpr hK
          rwa [Real.exp_log hK0] at this
        have hlow : Real.exp (δ / 2 * Real.log (n : ℝ) - 1) * c / 4
            ≤ lam ^ (2 * T) * (n : ℝ) * c / 4 := by
          have hmul : Real.exp (-((1 - δ / 2) * Real.log (n : ℝ) + 1)) * (n : ℝ)
              = Real.exp (δ / 2 * Real.log (n : ℝ) - 1) := by
            rw [show (δ / 2 * Real.log (n : ℝ) - 1)
                = (-((1 - δ / 2) * Real.log (n : ℝ) + 1)) + Real.log (n : ℝ) from by ring,
              Real.exp_add, Real.exp_log hnpos]
          have h1 : Real.exp (-((1 - δ / 2) * Real.log (n : ℝ) + 1)) * (n : ℝ)
              ≤ lam ^ (2 * T) * (n : ℝ) := mul_le_mul_of_nonneg_right hpow hnpos.le
          rw [hmul] at h1
          have hc4 : (0 : ℝ) ≤ c / 4 := by positivity
          nlinarith [h1, hc4]
        have hKlt : 4 * ε / (1 - ε) < Real.exp (δ / 2 * Real.log (n : ℝ) - 1) * c / 4 := by
          rw [hKdef] at hKexp
          rw [div_lt_iff₀ hε0']
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < (1 - ε) * c)] at hKexp
          nlinarith [hKexp, hc0, hε0']
        linarith
      have hTle := cyc_lower hn3 β hβ ε hε hε1 T hcond
      have hTcast : (T : ℝ) ≤ (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) := by exact_mod_cast hTle
      linarith
