-- Prove2me | solution 1 for MarkovMixing.relaxation_upper_aperiodic
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:12:57.619046+00:00
-- url     : https://prove2.me/submissions/17d0889f-439d-4474-aec9-3f2b24b29cd3

import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_spectral_representation
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace DirichletGap

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

lemma innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

lemma dirichlet_eq_inner {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by
  have hrow : ∀ x, ∑ y, P x y = 1 := hP.2
  have hcol : ∀ y, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have A : ∑ x, ∑ y, (g x) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hrow x, mul_one]
    ring
  have B : ∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hcol y]
    ring
  have C : ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y)
      = ∑ x : V, g x * (P.mulVec g) x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (P.mulVec g) x = ∑ y, P x y * g y from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hall : ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y)
      = (∑ x : V, ∑ y : V, (g x) ^ 2 * (π x * P x y))
        + (∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y))
        - 2 * ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  show 2⁻¹ * ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y) = _
  rw [hall, A, B, C]
  show _ = (∑ x : V, g x * g x * π x) - ∑ x : V, g x * (P.mulVec g) x * π x
  ring

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
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

lemma norm_eq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

lemma mulVec_expand (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by
  have e1 : ∀ y : V, P x y * g y = ∑ j, innerPi π g (ff j) * (P x y * ff j y) := by
    intro y
    have : ∀ j, innerPi π g (ff j) * (P x y * ff j y)
        = (innerPi π g (ff j) * ff j y) * P x y := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g y]
    ring
  show ∑ y : V, P x y * g y = _
  rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : V, P x y * ff j y = lam j * ff j x := by
    have := congrFun (heig j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [this]
  ring

lemma inner_mulVec (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * (P.mulVec g) x * π x
      = ∑ j, (innerPi π g (ff j) * lam j) * (g x * ff j x * π x) := by
    intro x
    rw [mulVec_expand heig hpos hcomp g x, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ x : V, g x * (P.mulVec g) x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * lam j * innerPi π g (ff j) = _
  ring

end Spectral

end DirichletGap

namespace RelUp

open DirichletGap

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma tvDist_le_l1 (μ ν : V → ℝ) : tvDist μ ν ≤ ∑ y, |μ y - ν y| := by
  refine ciSup_le fun A => ?_
  calc |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| = |∑ x ∈ A, (μ x - ν x)| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x ∈ A, |μ x - ν x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |μ x - ν x| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun i _ _ => abs_nonneg _

lemma distStationary_le' [Nonempty V] (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) (b : ℝ)
    (h : ∀ x, tvDist (rowDist P t x) π ≤ b) : distStationary P π t ≤ b :=
  ciSup_le h

end RelUp

open RelUp DirichletGap

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : MarkovMixing.Aperiodic P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (MarkovMixing.mixingTime P π ε : ℝ) ≤
      Real.log (1 / (ε * ⨅ x : V, π x)) * MarkovMixing.relaxationTime P + 1 := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [dirichlet_eq_inner hP hπ g, norm_eq hpos hcomp g, inner_mulVec heig hpos hcomp g,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : ∀ (a : Fin (Fintype.card V) → ℝ) (k : Fin (Fintype.card V)),
      innerPi π (fun x => ∑ j, a j * ff j x) (ff k) = a k := by
    intro a k
    have e : ∀ x : V, (∑ j, a j * ff j x) * ff k x * π x
        = ∑ j, a j * (ff j x * ff k x * π x) := by
      intro x
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    show ∑ x : V, (∑ j, a j * ff j x) * ff k x * π x = a k
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    have e2 : ∀ j, ∑ x : V, a j * (ff j x * ff k x * π x)
        = a j * (if j = k then 1 else 0) := by
      intro j
      rw [← Finset.mul_sum]
      exact congrArg _ (horth j k)
    rw [Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by simp [hb])]
    simp
  -- the constant function
  set one : V → ℝ := fun _ => 1 with hone_def
  have hPone : P.mulVec one = one := by
    funext x
    show ∑ y, P x y * 1 = 1
    simpa using hP.2 x
  have hone_eig : ∀ j, innerPi π one (ff j) * (lam j - 1) = 0 := by
    intro j
    have hA : P.mulVec one = fun x => ∑ k, (innerPi π one (ff k) * lam k) * ff k x := by
      funext x
      rw [mulVec_expand heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [expand hpos hcomp one (Classical.arbitrary V)] at h0
    exact one_ne_zero h0
  obtain ⟨j0, hj0⟩ := hc1
  have hlam0 : lam j0 = 1 := by
    rcases mul_eq_zero.mp (hone_eig j0) with h | h
    · exact absurd h hj0
    · linarith
  set x0 : V := Classical.arbitrary V with hx0_def
  have const_inner : ∀ u v : V → ℝ, (∀ x y : V, u x = u y) → (∀ x y : V, v x = v y) →
      innerPi π u v = u x0 * v x0 := by
    intro u v hu hv
    have e : ∀ x : V, u x * v x * π x = (u x0 * v x0) * π x := by
      intro x; rw [hu x x0, hv x x0]
    show ∑ x : V, u x * v x * π x = _
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hsum, mul_one]
  have hffconst : ∀ x y : V, ff j0 x = ff j0 y := by
    have h1 : P.mulVec (ff j0) = ff j0 := by
      rw [heig j0, hlam0, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j0) h1
  have ha : ff j0 x0 * ff j0 x0 = 1 := by
    have := horth j0 j0
    rw [const_inner _ _ hffconst hffconst] at this
    simpa using this
  have ha0 : ff j0 x0 ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hlamne : ∀ j, j ≠ j0 → lam j ≠ 1 := by
    intro j hj hlam1
    have h1 : P.mulVec (ff j) = ff j := by rw [heig j, hlam1, one_smul]
    have hcj : ∀ x y : V, ff j x = ff j y := (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) h1
    have hb : ff j x0 * ff j0 x0 = 0 := by
      have := horth j j0
      rw [const_inner _ _ hcj hffconst] at this
      simpa [hj] using this
    have hbb : ff j x0 * ff j x0 = 1 := by
      have := horth j j
      rw [const_inner _ _ hcj hcj] at this
      simpa using this
    have : ff j x0 = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h ha0
    rw [this] at hbb
    norm_num at hbb
  -- every eigenvalue other than 1 is one of the basis eigenvalues
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have h2 := horth j j
    rw [h] at h2
    simp [innerPi] at h2
  have heigval : ∀ l : ℝ, MarkovMixing.IsEigenvalue P l → l ≠ 1 →
      ∃ k, k ≠ j0 ∧ lam k = l := by
    rintro l ⟨gg, hg0, hg⟩ hl1
    have hex : ∃ k, innerPi π gg (ff k) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hg0
      funext z
      rw [← expand hpos hcomp gg z]
      exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    obtain ⟨k, hk⟩ := hex
    have hA : P.mulVec gg = fun z => ∑ j, (innerPi π gg (ff j) * lam j) * ff j z := by
      funext z
      rw [mulVec_expand heig hpos hcomp gg z]
    have hL : innerPi π (P.mulVec gg) (ff k) = innerPi π gg (ff k) * lam k := by
      rw [hA]; exact hcoef _ k
    have hR : innerPi π (P.mulVec gg) (ff k) = l * innerPi π gg (ff k) := by
      rw [hg]
      show ∑ z : V, (l • gg) z * ff k z * π z = l * ∑ z : V, gg z * ff k z * π z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp [Pi.smul_apply]; ring
    have hlamk : lam k = l := by
      have h3 : innerPi π gg (ff k) * lam k = innerPi π gg (ff k) * l := by rw [← hL, hR]; ring
      exact mul_left_cancel₀ hk h3
    refine ⟨k, ?_, hlamk⟩
    intro hc
    rw [hc, hlam0] at hlamk
    exact hl1 hlamk.symm
  have hb1 : ∀ r ∈ {r : ℝ | ∃ l : ℝ, MarkovMixing.IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|}, r ≤ 1 := by
    rintro r ⟨l, hl, -, rfl⟩
    exact (MarkovMixing.eigenvalue_basic P hP).1 l hl
  have hbddS : BddAbove {r : ℝ | ∃ l : ℝ, MarkovMixing.IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} :=
    ⟨1, hb1⟩
  have hmemS : ∀ j, j ≠ j0 →
      |lam j| ∈ {r : ℝ | ∃ l : ℝ, MarkovMixing.IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} :=
    fun j hj => ⟨lam j, ⟨ff j, hffne j, heig j⟩, hlamne j hj, rfl⟩
  have hstar_ge : ∀ j, j ≠ j0 → |lam j| ≤ MarkovMixing.lambdaStar P :=
    fun j hj => le_csSup hbddS (hmemS j hj)
  have hempty : (¬ ∃ j, j ≠ j0) →
      {r : ℝ | ∃ l : ℝ, MarkovMixing.IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} = ∅ := by
    intro hE
    push_neg at hE
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, hl, hl1, rfl⟩
    obtain ⟨k, hk, -⟩ := heigval l hl hl1
    exact hk (hE k)
  have hstar_nn : 0 ≤ MarkovMixing.lambdaStar P := by
    by_cases hE : ∃ j, j ≠ j0
    · obtain ⟨j, hj⟩ := hE
      exact le_trans (abs_nonneg _) (hstar_ge j hj)
    · show (0:ℝ) ≤ sSup _
      rw [hempty hE, Real.sSup_empty]
  have hstar_lt : MarkovMixing.lambdaStar P < 1 := by
    by_cases hE : ∃ j, j ≠ j0
    · obtain ⟨j1, hj1⟩ := hE
      have hne2 : (Finset.univ.erase j0).Nonempty :=
        ⟨j1, Finset.mem_erase.mpr ⟨hj1, Finset.mem_univ j1⟩⟩
      obtain ⟨js, hjs_mem, hjs⟩ :=
        Finset.exists_max_image (Finset.univ.erase j0) (fun j => |lam j|) hne2
      have hjsne : js ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
      have hub : ∀ r ∈ {r : ℝ | ∃ l : ℝ, MarkovMixing.IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|},
          r ≤ |lam js| := by
        rintro r ⟨l, hl, hl1, rfl⟩
        obtain ⟨k, hk, hkl⟩ := heigval l hl hl1
        rw [← hkl]
        exact hjs k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
      have h1 : MarkovMixing.lambdaStar P ≤ |lam js| :=
        csSup_le ⟨_, hmemS js hjsne⟩ hub
      have h2 : |lam js| ≤ 1 :=
        (MarkovMixing.eigenvalue_basic P hP).1 _ ⟨ff js, hffne js, heig js⟩
      have h3 : |lam js| ≠ 1 := by
        intro hc
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hc with h4 | h4
        · exact hlamne js hjsne h4
        · exact (MarkovMixing.eigenvalue_basic P hP).2.2 hirr hap
            ⟨ff js, hffne js, by rw [heig js, h4]⟩
      have : |lam js| < 1 := lt_of_le_of_ne h2 h3
      linarith
    · have : MarkovMixing.lambdaStar P = 0 := by
        show sSup _ = 0
        rw [hempty hE, Real.sSup_empty]
      rw [this]; norm_num
  -- the minimum of π
  obtain ⟨xm, -, hxmmin⟩ := Finset.exists_min_image (Finset.univ : Finset V) π
    ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hpmle : ∀ z : V, (⨅ y : V, π y) ≤ π z := fun z =>
    ciInf_le (Finite.bddBelow_range _) z
  have hpmpos : 0 < ⨅ y : V, π y :=
    lt_of_lt_of_le (hpos xm) (le_ciInf fun y => hxmmin y (Finset.mem_univ y))
  have hpmle1 : (⨅ y : V, π y) ≤ 1 := by
    refine le_trans (hpmle (Classical.arbitrary V)) ?_
    have h1 := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le)
      (Finset.mem_univ (Classical.arbitrary V))
    rw [hsum] at h1
    exact h1
  -- the pointwise spectral estimate
  have hnormx : ∀ z : V, ∑ j, ff j z ^ 2 = 1 / π z := by
    intro z
    have h1 : ∑ j, ff j z * ff j z = 1 / π z := by
      have h2 := hcomp z z
      simpa using h2
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hkey : ∀ (t : ℕ) (x y : V),
      |(P ^ t) x y / π y - 1| ≤ MarkovMixing.lambdaStar P ^ t / (⨅ y : V, π y) := by
    intro t x y
    have hj0term : ff j0 x * ff j0 y * lam j0 ^ t = 1 := by
      rw [hlam0, one_pow, mul_one, hffconst x x0, hffconst y x0]
      exact ha
    have hsplit : (P ^ t) x y / π y - 1
        = ∑ j ∈ Finset.univ.erase j0, ff j x * ff j y * lam j ^ t := by
      rw [hspec t x y, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hj0term]
      ring
    have hbnd : ∑ j ∈ Finset.univ.erase j0, |ff j x| * |ff j y| ≤ 1 / (⨅ y : V, π y) := by
      have h1 : ∀ j, |ff j x| * |ff j y| ≤ (ff j x ^ 2 + ff j y ^ 2) / 2 := by
        intro j
        nlinarith [sq_nonneg (|ff j x| - |ff j y|), sq_abs (ff j x), sq_abs (ff j y)]
      have h2 : ∑ j, (ff j x ^ 2 + ff j y ^ 2) / 2 = (1 / π x + 1 / π y) / 2 := by
        have e : ∀ j, (ff j x ^ 2 + ff j y ^ 2) / 2 = ff j x ^ 2 / 2 + ff j y ^ 2 / 2 :=
          fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.sum_div,
          ← Finset.sum_div, hnormx x, hnormx y]
        ring
      calc ∑ j ∈ Finset.univ.erase j0, |ff j x| * |ff j y|
          ≤ ∑ j ∈ Finset.univ.erase j0, (ff j x ^ 2 + ff j y ^ 2) / 2 :=
            Finset.sum_le_sum fun j _ => h1 j
        _ ≤ ∑ j, (ff j x ^ 2 + ff j y ^ 2) / 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun i _ _ => by positivity)
        _ = (1 / π x + 1 / π y) / 2 := h2
        _ ≤ 1 / (⨅ y : V, π y) := by
            have e1 : 1 / π x ≤ 1 / (⨅ y : V, π y) :=
              one_div_le_one_div_of_le hpmpos (hpmle x)
            have e2 : 1 / π y ≤ 1 / (⨅ y : V, π y) :=
              one_div_le_one_div_of_le hpmpos (hpmle y)
            linarith
    rw [hsplit]
    calc |∑ j ∈ Finset.univ.erase j0, ff j x * ff j y * lam j ^ t|
        ≤ ∑ j ∈ Finset.univ.erase j0, |ff j x * ff j y * lam j ^ t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase j0, (|ff j x| * |ff j y|) * MarkovMixing.lambdaStar P ^ t := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul, abs_mul, abs_pow]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          exact pow_le_pow_left₀ (abs_nonneg _)
            (hstar_ge j (Finset.mem_erase.mp hj).1) t
      _ = (∑ j ∈ Finset.univ.erase j0, |ff j x| * |ff j y|)
            * MarkovMixing.lambdaStar P ^ t := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 / (⨅ y : V, π y)) * MarkovMixing.lambdaStar P ^ t :=
          mul_le_mul_of_nonneg_right hbnd (pow_nonneg hstar_nn t)
      _ = MarkovMixing.lambdaStar P ^ t / (⨅ y : V, π y) := by ring
  -- the distance bound
  have hd : ∀ t : ℕ, MarkovMixing.distStationary P π t
      ≤ MarkovMixing.lambdaStar P ^ t / (⨅ y : V, π y) := by
    intro t
    refine RelUp.distStationary_le' P π t _ fun x => ?_
    refine le_trans (RelUp.tvDist_le_l1 _ _) ?_
    have e : ∀ y : V, |MarkovMixing.rowDist P t x y - π y|
        = π y * |(P ^ t) x y / π y - 1| := by
      intro y
      have hy := (hpos y).ne'
      have h3 : π y * ((P ^ t) x y / π y - 1) = (P ^ t) x y - π y := by field_simp
      show |(P ^ t) x y - π y| = _
      rw [← h3, abs_mul, abs_of_pos (hpos y)]
    rw [Finset.sum_congr rfl (fun y _ => e y)]
    calc ∑ y, π y * |(P ^ t) x y / π y - 1|
        ≤ ∑ y : V, π y * (MarkovMixing.lambdaStar P ^ t / (⨅ y : V, π y)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hkey t x y) (hpos y).le
      _ = MarkovMixing.lambdaStar P ^ t / (⨅ y : V, π y) := by
          rw [← Finset.sum_mul, hsum, one_mul]
  -- calculus
  have hgs : 0 < 1 - MarkovMixing.lambdaStar P := by linarith
  have htrel : MarkovMixing.relaxationTime P = (1 - MarkovMixing.lambdaStar P)⁻¹ := rfl
  have htrelpos : 0 < MarkovMixing.relaxationTime P := by rw [htrel]; positivity
  have hKpos : 0 < Real.log (1 / (ε * ⨅ x : V, π x)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hpmpos, hpmle1]
  set K : ℝ := Real.log (1 / (ε * ⨅ x : V, π x)) with hK_def
  set T : ℕ := ⌈K * MarkovMixing.relaxationTime P⌉₊ with hT_def
  have hTle : K * MarkovMixing.relaxationTime P ≤ (T : ℝ) := Nat.le_ceil _
  have hTlt : (T : ℝ) < K * MarkovMixing.relaxationTime P + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hexpK : Real.exp K = 1 / (ε * ⨅ x : V, π x) := Real.exp_log (by positivity)
  have hdT : MarkovMixing.distStationary P π T ≤ ε := by
    refine le_trans (hd T) ?_
    have h1 : MarkovMixing.lambdaStar P ≤ Real.exp (MarkovMixing.lambdaStar P - 1) := by
      have := Real.add_one_le_exp (MarkovMixing.lambdaStar P - 1)
      linarith
    have h2 : MarkovMixing.lambdaStar P ^ T ≤ Real.exp ((MarkovMixing.lambdaStar P - 1) * T) := by
      calc MarkovMixing.lambdaStar P ^ T
          ≤ (Real.exp (MarkovMixing.lambdaStar P - 1)) ^ T :=
            pow_le_pow_left₀ hstar_nn h1 T
        _ = Real.exp ((MarkovMixing.lambdaStar P - 1) * T) := by
            rw [← Real.exp_nat_mul]
            ring_nf
    have h3 : (MarkovMixing.lambdaStar P - 1) * T ≤ -K := by
      have h4 : K ≤ (1 - MarkovMixing.lambdaStar P) * T := by
        have h5 : K * MarkovMixing.relaxationTime P * (1 - MarkovMixing.lambdaStar P) ≤
            (T : ℝ) * (1 - MarkovMixing.lambdaStar P) :=
          mul_le_mul_of_nonneg_right hTle hgs.le
        have h6 : K * MarkovMixing.relaxationTime P * (1 - MarkovMixing.lambdaStar P) = K := by
          rw [htrel]; field_simp
        linarith [h5, h6]
      nlinarith
    have h7 : MarkovMixing.lambdaStar P ^ T ≤ ε * (⨅ x : V, π x) := by
      calc MarkovMixing.lambdaStar P ^ T
          ≤ Real.exp ((MarkovMixing.lambdaStar P - 1) * T) := h2
        _ ≤ Real.exp (-K) := Real.exp_le_exp.mpr h3
        _ = ε * (⨅ x : V, π x) := by
            rw [Real.exp_neg, hexpK]
            field_simp
    rw [div_le_iff₀ hpmpos]
    calc MarkovMixing.lambdaStar P ^ T ≤ ε * (⨅ x : V, π x) := h7
      _ = ε * (⨅ x : V, π x) := rfl
  have hmix : MarkovMixing.mixingTime P π ε ≤ T := Nat.sInf_le hdT
  calc (MarkovMixing.mixingTime P π ε : ℝ) ≤ (T : ℝ) := by exact_mod_cast hmix
    _ ≤ K * MarkovMixing.relaxationTime P + 1 := le_of_lt hTlt
