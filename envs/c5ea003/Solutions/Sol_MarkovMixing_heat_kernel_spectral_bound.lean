-- Prove2me | solution 1 for MarkovMixing.heat_kernel_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T20:12:10.3969+00:00
-- url     : https://prove2.me/submissions/a5684f76-7758-4482-9603-e5d6743185f2

import Definitions.Def_mm_continuous
import Theorems.Thm_MarkovMixing_spectral_representation
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace HeatSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

/-- The Poissonized geometric series: `∑_k e^{-t} t^k/k! λ^k = e^{-t} e^{tλ}`. -/
lemma hasSum_poisson (t lam : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-t) * t ^ k / (Nat.factorial k) * lam ^ k)
      (Real.exp (-t) * Real.exp (t * lam)) := by
  have h0 : HasSum (fun k : ℕ => (t * lam) ^ k / (Nat.factorial k))
      (Real.exp (t * lam)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (t * lam)
  have h1 := h0.mul_left (Real.exp (-t))
  have hfun : (fun k : ℕ => Real.exp (-t) * t ^ k / (Nat.factorial k) * lam ^ k)
      = fun k : ℕ => Real.exp (-t) * ((t * lam) ^ k / (Nat.factorial k)) := by
    funext k
    rw [mul_pow]
    ring
  rw [hfun]
  exact h1

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ a b : V, ∑ j, ff j a * ff j b = (if a = b then 1 else 0) / π b)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by
  have e1 : ∀ j, innerPi π g (ff j) * ff j x = ∑ y : V, g y * π y * (ff j y * ff j x) := by
    intro j
    show (∑ y : V, g y * ff j y * π y) * ff j x = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  have e2 : ∀ y : V, ∑ j, g y * π y * (ff j y * ff j x)
      = g y * π y * ((if y = x then 1 else 0) / π x) := by
    intro y
    rw [← Finset.mul_sum, hcomp y x]
  rw [Finset.sum_congr rfl (fun y _ => e2 y),
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [hb])]
  have hx := (hpos x).ne'
  field_simp
  simp

end Spectral

end HeatSpec

open HeatSpec

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ)
    (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) (x y : V) (t : ℝ) (ht : 0 ≤ t) :
    |MarkovMixing.heatKernel P t x y - π y| ≤
      Real.sqrt (π y / π x) * Real.exp (-(MarkovMixing.spectralGap P) * t) := by
  classical
  have hpos := pi_pos hirr hπ hP
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  -- completeness relation, from `t = 0`
  have hcomp : ∀ a b : V, ∑ j, ff j a * ff j b = (if a = b then 1 else 0) / π b := by
    intro a b
    have h := hspec 0 a b
    simpa [Matrix.one_apply] using h.symm
  -- the spectral expansion of the powers, cleared of the division
  have hpk : ∀ (k : ℕ) (a b : V),
      (P ^ k) a b = (∑ j, ff j a * ff j b * lam j ^ k) * π b := by
    intro k a b
    have h := hspec k a b
    rw [div_eq_iff (hpos b).ne'] at h
    exact h
  -- eigenfunctions are nonzero, so each `lam j` really is an eigenvalue
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j hj
    have := horth j j
    rw [hj] at this
    simp [innerPi] at this
  have hev : ∀ j, MarkovMixing.IsEigenvalue P (lam j) := fun j => ⟨ff j, hffne j, heig j⟩
  have hbdd : BddAbove {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} := by
    refine ⟨1, fun l hl => ?_⟩
    exact (abs_le.mp ((MarkovMixing.eigenvalue_basic P hP).1 l hl.1)).2
  have hlam2 : ∀ j, lam j ≠ 1 → lam j ≤ MarkovMixing.lambdaTwo P := by
    intro j hj
    exact le_csSup hbdd ⟨hev j, hj⟩
  -- the heat kernel, expanded spectrally
  set w : Fin (Fintype.card V) → ℝ := fun j => Real.exp (-t) * Real.exp (t * lam j) with hwdef
  have hwexp : ∀ j : Fin (Fintype.card V), w j = Real.exp (t * (lam j - 1)) := by
    intro j
    show Real.exp (-t) * Real.exp (t * lam j) = Real.exp (t * (lam j - 1))
    rw [← Real.exp_add]
    ring_nf
  have hHK : MarkovMixing.heatKernel P t x y = ∑ j, ff j x * ff j y * π y * w j := by
    have hterm : ∀ k : ℕ, Real.exp (-t) * t ^ k / (Nat.factorial k) * (P ^ k) x y
        = ∑ j, (ff j x * ff j y * π y) *
            (Real.exp (-t) * t ^ k / (Nat.factorial k) * lam j ^ k) := by
      intro k
      rw [hpk k x y, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hs : HasSum (fun k : ℕ => Real.exp (-t) * t ^ k / (Nat.factorial k) * (P ^ k) x y)
        (∑ j, ff j x * ff j y * π y * w j) := by
      have h2 : HasSum (fun k : ℕ => ∑ j, (ff j x * ff j y * π y) *
            (Real.exp (-t) * t ^ k / (Nat.factorial k) * lam j ^ k))
          (∑ j, (ff j x * ff j y * π y) * (Real.exp (-t) * Real.exp (t * lam j))) :=
        hasSum_sum fun j _ => (hasSum_poisson t (lam j)).mul_left _
      have h3 : (∑ j, (ff j x * ff j y * π y) * (Real.exp (-t) * Real.exp (t * lam j)))
          = ∑ j, ff j x * ff j y * π y * w j := rfl
      rw [← h3]
      exact (funext hterm) ▸ h2
    exact hs.tsum_eq
  -- the eigenvalue-one block
  set J : Finset (Fin (Fintype.card V)) := Finset.univ.filter (fun j => lam j = 1) with hJdef
  have hconst : ∀ j ∈ J, ∀ a b : V, ff j a = ff j b := by
    intro j hj a b
    have hl : lam j = 1 := (Finset.mem_filter.mp hj).2
    have hfix : P.mulVec (ff j) = ff j := by rw [heig j, hl, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) hfix a b
  have hcmean : ∀ j : Fin (Fintype.card V), innerPi π (fun _ => (1 : ℝ)) (ff j) = ∑ a, ff j a * π a := by
    intro j
    show ∑ a, (1:ℝ) * ff j a * π a = ∑ a, ff j a * π a
    exact Finset.sum_congr rfl fun a _ => by ring
  have hceig : ∀ j : Fin (Fintype.card V), lam j * (∑ a, ff j a * π a) = ∑ a, ff j a * π a := by
    intro j
    have hL : ∑ a, (P.mulVec (ff j)) a * π a = ∑ b, ff j b * π b := by
      have e : ∀ a : V, (P.mulVec (ff j)) a * π a = ∑ b, π a * P a b * ff j b := by
        intro a
        show (∑ b, P a b * ff j b) * π a = _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul]
      have : ∑ a, π a * P a b = π b := congrFun hπ.2 b
      rw [this]
      ring
    have e2 : ∑ a, (P.mulVec (ff j)) a * π a = lam j * ∑ a, ff j a * π a := by
      rw [heig j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by simp [mul_assoc]
    rw [← e2, hL]
  have hczero : ∀ j : Fin (Fintype.card V), j ∉ J → (∑ a, ff j a * π a) = 0 := by
    intro j hj
    have hne : lam j ≠ 1 := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    have := hceig j
    have h2 : (lam j - 1) * (∑ a, ff j a * π a) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (by linarith : lam j = 1) hne
    · exact h
  have hJsum : ∑ j ∈ J, ff j x * ff j y = 1 := by
    have hexp := expand hpos hcomp (fun _ => (1 : ℝ)) x
    have hrw : ∑ j, innerPi π (fun _ => (1 : ℝ)) (ff j) * ff j x
        = ∑ j ∈ J, ff j x * ff j y := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => lam j = 1)]
      have hzero : ∑ j ∈ Finset.univ.filter (fun j => ¬ lam j = 1),
          innerPi π (fun _ => (1 : ℝ)) (ff j) * ff j x = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have : j ∉ J := by
          intro hc
          have h1 := (Finset.mem_filter.mp hj).2
          have h2 := (Finset.mem_filter.mp hc).2
          exact h1 h2
        rw [hcmean j, hczero j this, zero_mul]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjJ : j ∈ J := hj
      have hsum1 : ∑ a, π a = 1 := hπ.1.2
      have : ∑ a, ff j a * π a = ff j x := by
        have e : ∀ a : V, ff j a * π a = ff j x * π a := fun a => by
          rw [hconst j hjJ a x]
        rw [Finset.sum_congr rfl (fun a _ => e a), ← Finset.mul_sum, hsum1, mul_one]
      rw [hcmean j, this, hconst j hjJ y x]
    rw [← hrw, hexp]
  -- split off the eigenvalue-one block
  have hwJ : ∀ j ∈ J, w j = 1 := by
    intro j hj
    have hl : lam j = 1 := (Finset.mem_filter.mp hj).2
    rw [hwexp j, hl]
    simp
  have hsplit : MarkovMixing.heatKernel P t x y - π y
      = π y * ∑ j ∈ Finset.univ.filter (fun j => ¬ lam j = 1), ff j x * ff j y * w j := by
    rw [hHK, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => lam j = 1)]
    have hA : ∑ j ∈ J, ff j x * ff j y * π y * w j = π y := by
      have e : ∀ j ∈ J, ff j x * ff j y * π y * w j = (ff j x * ff j y) * π y := by
        intro j hj
        rw [hwJ j hj, mul_one]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hJsum, one_mul]
    rw [hA]
    rw [Finset.mul_sum]
    have e2 : ∀ j ∈ Finset.univ.filter (fun j => ¬ lam j = 1),
        ff j x * ff j y * π y * w j = π y * (ff j x * ff j y * w j) := fun j _ => by ring
    rw [Finset.sum_congr rfl e2]
    ring
  -- bound the remaining block
  set K : Finset (Fin (Fintype.card V)) := Finset.univ.filter (fun j => ¬ lam j = 1) with hKdef
  set G : ℝ := Real.exp (-(MarkovMixing.spectralGap P) * t) with hGdef
  have hwK : ∀ j ∈ K, 0 < w j ∧ w j ≤ G := by
    intro j hj
    have hne : lam j ≠ 1 := (Finset.mem_filter.mp hj).2
    refine ⟨by rw [hwexp j]; exact Real.exp_pos _, ?_⟩
    rw [hwexp j, hGdef]
    apply Real.exp_le_exp.mpr
    have h1 : lam j ≤ MarkovMixing.lambdaTwo P := hlam2 j hne
    have : -(MarkovMixing.spectralGap P) = MarkovMixing.lambdaTwo P - 1 := by
      rw [MarkovMixing.spectralGap]; ring
    rw [this]
    nlinarith [ht]
  have hA : |∑ j ∈ K, ff j x * ff j y * w j| ≤ G * ∑ j ∈ K, |ff j x| * |ff j y| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hw1, hw2⟩ := hwK j hj
    rw [abs_mul, abs_mul, abs_of_pos hw1]
    have h0 : 0 ≤ |ff j x| * |ff j y| := by positivity
    nlinarith [h0, hw1, hw2]
  -- Cauchy-Schwarz for the surviving coefficients
  have hCS : ∑ j ∈ K, |ff j x| * |ff j y| ≤ Real.sqrt (1 / (π x * π y)) := by
    have hsq : (∑ j ∈ K, |ff j x| * |ff j y|) ^ 2 ≤ 1 / (π x * π y) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq K (fun j => |ff j x|) (fun j => |ff j y|)
      have h2 : ∀ (a : V), ∑ j ∈ K, |ff j a| ^ 2 ≤ 1 / π a := by
        intro a
        have hall : ∑ j, ff j a * ff j a = 1 / π a := by
          have := hcomp a a
          simpa using this
        have hsub : ∑ j ∈ K, |ff j a| ^ 2 ≤ ∑ j, |ff j a| ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) ?_
          intro i _ _
          positivity
        have heq : ∑ j, |ff j a| ^ 2 = ∑ j, ff j a * ff j a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sq_abs]
          ring
        rw [heq, hall] at hsub
        exact hsub
      have hx1 := h2 x
      have hy1 := h2 y
      have hnn : (0:ℝ) ≤ ∑ j ∈ K, |ff j y| ^ 2 :=
        Finset.sum_nonneg fun i _ => by positivity
      calc (∑ j ∈ K, |ff j x| * |ff j y|) ^ 2
          ≤ (∑ j ∈ K, |ff j x| ^ 2) * ∑ j ∈ K, |ff j y| ^ 2 := h1
        _ ≤ (1 / π x) * (1 / π y) := by
            have hnn2 : (0:ℝ) ≤ ∑ j ∈ K, |ff j x| ^ 2 :=
              Finset.sum_nonneg fun i _ => by positivity
            have hpx : (0:ℝ) < 1 / π x := one_div_pos.mpr (hpos x)
            nlinarith
        _ = 1 / (π x * π y) := by field_simp
    have hnn : (0:ℝ) ≤ ∑ j ∈ K, |ff j x| * |ff j y| :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ∑ j ∈ K, |ff j x| * |ff j y|
        = Real.sqrt ((∑ j ∈ K, |ff j x| * |ff j y|) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (1 / (π x * π y)) := Real.sqrt_le_sqrt hsq
  -- assemble
  have hfin : π y * Real.sqrt (1 / (π x * π y)) = Real.sqrt (π y / π x) := by
    have hx := (hpos x).ne'
    have hy := (hpos y).ne'
    have hrw : π y / π x = (π y) ^ 2 * (1 / (π x * π y)) := by
      field_simp
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (hpos y).le]
  rw [hsplit, abs_mul, abs_of_pos (hpos y)]
  have hGpos : 0 < G := Real.exp_pos _
  calc π y * |∑ j ∈ K, ff j x * ff j y * w j|
      ≤ π y * (G * ∑ j ∈ K, |ff j x| * |ff j y|) := by
        exact mul_le_mul_of_nonneg_left hA (hpos y).le
    _ ≤ π y * (G * Real.sqrt (1 / (π x * π y))) := by
        have := mul_le_mul_of_nonneg_left hCS hGpos.le
        exact mul_le_mul_of_nonneg_left this (hpos y).le
    _ = (π y * Real.sqrt (1 / (π x * π y))) * G := by ring
    _ = Real.sqrt (π y / π x) * G := by rw [hfin]
