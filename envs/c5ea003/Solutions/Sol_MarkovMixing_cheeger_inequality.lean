-- Prove2me | solution 1 for MarkovMixing.cheeger_inequality
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:03:03.511539+00:00
-- url     : https://prove2.me/submissions/ec2aaf1f-9f41-4e9d-b907-ad1fb8d7500d

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_spectral_representation
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Theorems.Thm_MarkovMixing_cheeger_upper
import Theorems.Thm_MarkovMixing_bottleneck_coarea
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

namespace Cheeger

open DirichletGap

/-- For an irreducible reversible chain with at least two states, `λ₂` is an
eigenvalue, realised by an eigenfunction of unit `ℓ²(π)`-norm and mean zero. -/
lemma exists_lambdaTwo_eigen {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
      P.mulVec g = (MarkovMixing.lambdaTwo P) • g := by
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
  -- the second-largest eigenvalue
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jstar, hjs_mem, hjs⟩ := Finset.exists_max_image (Finset.univ.erase j0) lam hne
  have hjs_ne : jstar ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have := horth j j
    rw [h] at this
    simp [innerPi] at this
  have hgap : MarkovMixing.spectralGap P = 1 - lam jstar := by
    have hmem : lam jstar ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} :=
      ⟨⟨ff jstar, hffne jstar, heig jstar⟩, hlamne jstar hjs_ne⟩
    have hbdd : ∀ r ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1}, r ≤ lam jstar := by
      rintro r ⟨⟨g, hg0, hg⟩, hr1⟩
      have hex : ∃ k, innerPi π g (ff k) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hg0
        funext x
        rw [← expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [mulVec_expand heig hpos hcomp g x]
      have hL : innerPi π (P.mulVec g) (ff k) = innerPi π g (ff k) * lam k := by
        rw [hA]; exact hcoef _ k
      have hR : innerPi π (P.mulVec g) (ff k) = r * innerPi π g (ff k) := by
        rw [hg]
        show ∑ x : V, (r • g) x * ff k x * π x = r * ∑ x : V, g x * ff k x * π x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply]; ring
      have hlamk : lam k = r := by
        have : innerPi π g (ff k) * lam k = innerPi π g (ff k) * r := by rw [← hL, hR]; ring
        exact mul_left_cancel₀ hk this
      have hkne : k ≠ j0 := by
        intro h; rw [h, hlam0] at hlamk; exact hr1 hlamk.symm
      rw [← hlamk]
      exact hjs k (Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩)
    show 1 - MarkovMixing.lambdaTwo P = 1 - lam jstar
    rw [show MarkovMixing.lambdaTwo P = lam jstar from
      le_antisymm (csSup_le ⟨_, hmem⟩ hbdd) (le_csSup ⟨lam jstar, hbdd⟩ hmem)]
  -- the minimiser
  have hfs_exp : MarkovMixing.distExp π (ff jstar) = 0 := by
    have h1 : innerPi π (ff jstar) (ff j0) = ff j0 x0 * MarkovMixing.distExp π (ff jstar) := by
      have e : ∀ x : V, ff jstar x * ff j0 x * π x = ff j0 x0 * (ff jstar x * π x) := by
        intro x; rw [hffconst x x0]; ring
      show ∑ x : V, ff jstar x * ff j0 x * π x = _
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      rfl
    rw [horth jstar j0] at h1
    simp [hjs_ne] at h1
    rcases h1 with h | h
    · exact absurd h ha0
    · exact h
  have hfs_norm : innerPi π (ff jstar) (ff jstar) = 1 := by simpa using horth jstar jstar
  refine ⟨ff jstar, hfs_norm, hfs_exp, ?_⟩
  have : MarkovMixing.lambdaTwo P = lam jstar := by
    have h1 : MarkovMixing.spectralGap P = 1 - MarkovMixing.lambdaTwo P := rfl
    rw [h1] at hgap
    linarith
  rw [this]
  exact heig jstar

end Cheeger

namespace Cheeger2

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V] {P : Matrix V V ℝ} {π : V → ℝ}

lemma edge_symm (hrev : DetailedBalance P π) (x y : V) :
    edgeMeasure P π x y = edgeMeasure P π y x := hrev x y

lemma edge_nonneg (hP : IsStochastic P) (hpos : ∀ x, 0 < π x) (x y : V) :
    0 ≤ edgeMeasure P π x y := mul_nonneg (hpos x).le (hP.1 x y)

lemma swap_sum (hrev : DetailedBalance P π) (F : V → V → ℝ) :
    ∑ x, ∑ y, F x y * edgeMeasure P π x y = ∑ x, ∑ y, F y x * edgeMeasure P π x y := by
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [edge_symm hrev x y]

lemma sum_left (hP : IsStochastic P) (f : V → ℝ) :
    ∑ x, ∑ y, f x ^ 2 * edgeMeasure P π x y = innerPi π f f := by
  have e : ∀ x : V, ∑ y, f x ^ 2 * edgeMeasure P π x y = f x * f x * π x := by
    intro x
    show ∑ y, f x ^ 2 * (π x * P x y) = _
    have : ∀ y : V, f x ^ 2 * (π x * P x y) = (f x ^ 2 * π x) * P x y := fun y => by ring
    rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum, hP.2 x, mul_one]
    ring
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  rfl

lemma sum_right (hπ : IsStationary P π) (f : V → ℝ) :
    ∑ x, ∑ y, f y ^ 2 * edgeMeasure P π x y = innerPi π f f := by
  rw [Finset.sum_comm]
  have hcol : ∀ y : V, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have e : ∀ y : V, ∑ x, f y ^ 2 * edgeMeasure P π x y = f y * f y * π y := by
    intro y
    show ∑ x, f y ^ 2 * (π x * P x y) = _
    rw [← Finset.mul_sum, hcol y]
    ring
  rw [Finset.sum_congr rfl (fun y _ => e y)]
  rfl

lemma sum_diff (f : V → ℝ) :
    ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y = 2 * dirichletForm P π f := by
  have hd : dirichletForm P π f = 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := rfl
  rw [hd]
  ring

lemma sum_add_sq (hP : IsStochastic P) (hπ : IsStationary P π) (f : V → ℝ) :
    ∑ x, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 4 * innerPi π f f - 2 * dirichletForm P π f := by
  have e : ∀ x y : V, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 2 * (f x ^ 2 * edgeMeasure P π x y) + 2 * (f y ^ 2 * edgeMeasure P π x y)
        - (f x - f y) ^ 2 * edgeMeasure P π x y := fun x y => by ring
  have e2 : ∀ x : V, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 2 * (∑ y, f x ^ 2 * edgeMeasure P π x y) + 2 * (∑ y, f y ^ 2 * edgeMeasure P π x y)
        - ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => e x y
  rw [Finset.sum_congr rfl (fun x _ => e2 x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_left hP f, sum_right hπ f, sum_diff f]
  ring

lemma pos_part_sq (f : V → ℝ) (hrev : DetailedBalance P π) :
    ∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * edgeMeasure P π x y = dirichletForm P π f := by
  have hswap := swap_sum hrev (fun x y => (max (f x - f y) 0) ^ 2)
  have hpt : ∀ x y : V, (max (f x - f y) 0) ^ 2 + (max (f y - f x) 0) ^ 2 = (f x - f y) ^ 2 := by
    intro x y
    rcases le_or_gt (f y) (f x) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hsum : (∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * edgeMeasure P π x y)
      + (∑ x, ∑ y, (max (f y - f x) 0) ^ 2 * edgeMeasure P π x y)
      = ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← add_mul, hpt x y]
  rw [sum_diff f] at hsum
  linarith [hswap, hsum]

lemma add_part_sq_le (hP : IsStochastic P) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    ∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0) * edgeMeasure P π x y
      ≤ 2 * innerPi π f f - dirichletForm P π f := by
  have hswap := swap_sum hrev (fun x y => if f y < f x then (f x + f y) ^ 2 else 0)
  have hpt : ∀ x y : V, (if f y < f x then (f x + f y) ^ 2 else 0)
      + (if f x < f y then (f y + f x) ^ 2 else 0) ≤ (f x + f y) ^ 2 := by
    intro x y
    rcases lt_trichotomy (f x) (f y) with h | h | h
    · rw [if_neg (by linarith), if_pos h, zero_add]
      have : (f y + f x) ^ 2 = (f x + f y) ^ 2 := by ring
      linarith [this.le, this.ge]
    · rw [if_neg (by linarith), if_neg (by linarith)]
      nlinarith [sq_nonneg (f x + f y)]
    · rw [if_pos h, if_neg (by linarith)]
      linarith
  have hle : (∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0) * edgeMeasure P π x y)
      + (∑ x, ∑ y, (if f x < f y then (f y + f x) ^ 2 else 0) * edgeMeasure P π x y)
      ≤ ∑ x, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (hpt x y) (edge_nonneg hP hpos x y)
  rw [sum_add_sq hP hπ f] at hle
  linarith [hswap, hle]

end Cheeger2

open Cheeger Cheeger2 DirichletGap

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.bottleneckStar P π ^ 2 / 2 ≤ MarkovMixing.spectralGap P ∧
    MarkovMixing.spectralGap P ≤ 2 * MarkovMixing.bottleneckStar P π := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x, π x = 1 := hπ.1.2
  have hQnn : ∀ x y : V, 0 ≤ MarkovMixing.edgeMeasure P π x y := fun x y =>
    edge_nonneg hP hpos x y
  have hrow : ∀ x : V, ∑ y, MarkovMixing.edgeMeasure P π x y = π x := by
    intro x
    show ∑ y, π x * P x y = π x
    rw [← Finset.mul_sum, hP.2 x, mul_one]
  -- the family of bottleneck ratios
  have hbdd : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
      MarkovMixing.bottleneckRatio P π S.1) := by
    refine ⟨0, ?_⟩
    rintro b ⟨S, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y)
      (Finset.sum_nonneg fun x _ => (hpos x).le)
  have hsub : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := by
    obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ 2⁻¹ := by
      by_contra hcon
      push_neg at hcon
      have hcard : 1 < Fintype.card V := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have h1 : π x + π y ≤ ∑ z, π z := by
        calc π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := (Finset.sum_pair hxy).symm
          _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => (hpos i).le)
      have := hcon x
      have := hcon y
      linarith
    exact ⟨⟨{x}, ⟨Finset.singleton_nonempty x, by simpa using hx⟩⟩⟩
  have hΦnn : 0 ≤ MarkovMixing.bottleneckStar P π := by
    refine le_ciInf fun S => ?_
    exact div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y)
      (Finset.sum_nonneg fun x _ => (hpos x).le)
  have hΦle1 : MarkovMixing.bottleneckStar P π ≤ 1 := by
    obtain ⟨S⟩ := hsub
    refine le_trans (ciInf_le hbdd S) ?_
    obtain ⟨T, hTne, hThalf⟩ := S
    have hppos : 0 < ∑ x ∈ T, π x := by
      obtain ⟨x, hx⟩ := hTne
      have h1 : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    show (∑ x ∈ T, ∑ y ∈ Tᶜ, MarkovMixing.edgeMeasure P π x y) / (∑ x ∈ T, π x) ≤ 1
    rw [div_le_one hppos]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← hrow x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hQnn x i)
  refine ⟨?_, MarkovMixing.cheeger_upper hV P hP hirr π hπ hrev⟩
  rcases le_or_gt (1/2 : ℝ) (MarkovMixing.spectralGap P) with hg | hg
  · nlinarith [mul_le_mul hΦle1 hΦle1 hΦnn zero_le_one]
  -- the interesting case
  obtain ⟨g0, hg0norm, hg0exp, hg0eig⟩ := exists_lambdaTwo_eigen hV P hP hirr π hπ hrev
  obtain ⟨g, hgnorm, hgexp, hgeig, hgsupp⟩ :
      ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
        P.mulVec g = (MarkovMixing.lambdaTwo P) • g ∧
        ∑ x ∈ Finset.univ.filter (fun x : V => 0 < g x), π x ≤ 2⁻¹ := by
    by_cases hc : ∑ x ∈ Finset.univ.filter (fun x : V => 0 < g0 x), π x ≤ 2⁻¹
    · exact ⟨g0, hg0norm, hg0exp, hg0eig, hc⟩
    · push_neg at hc
      refine ⟨fun x => -g0 x, ?_, ?_, ?_, ?_⟩
      · show ∑ x, (-g0 x) * (-g0 x) * π x = 1
        rw [← hg0norm]
        exact Finset.sum_congr rfl fun x _ => by ring
      · show ∑ x, (-g0 x) * π x = 0
        have : ∑ x, (-g0 x) * π x = -∑ x, g0 x * π x := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
        rw [this]
        show -MarkovMixing.distExp π g0 = 0
        rw [hg0exp, neg_zero]
      · funext x
        have h1 := congrFun hg0eig x
        show ∑ y, P x y * (-g0 y) = _
        have h2 : ∑ y, P x y * (-g0 y) = -∑ y, P x y * g0 y := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [h2]
        simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
        show -(∑ y, P x y * g0 y) = _
        rw [show ∑ y, P x y * g0 y = P.mulVec g0 x from rfl, h1]
        ring
      · have hdisj : Disjoint (Finset.univ.filter (fun x : V => 0 < g0 x))
            (Finset.univ.filter (fun x : V => 0 < -g0 x)) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          linarith
        have hle : (∑ x ∈ Finset.univ.filter (fun x : V => 0 < g0 x), π x)
            + ∑ x ∈ Finset.univ.filter (fun x : V => 0 < -g0 x), π x ≤ 1 := by
          rw [← Finset.sum_union hdisj, ← hsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => (hpos i).le)
        linarith
  -- the positive part of the eigenfunction
  set f : V → ℝ := fun x => max (g x) 0 with hf_def
  have hfnn : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hfge : ∀ x, g x ≤ f x := fun x => le_max_left _ _
  set N : ℝ := MarkovMixing.innerPi π f f with hN_def
  set E : ℝ := MarkovMixing.dirichletForm P π f with hE_def
  have hEnn : 0 ≤ E := by
    rw [hE_def]
    show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y)
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hP.1 x y))
  have hgexists : ∃ x, 0 < g x := by
    by_contra hcon
    push_neg at hcon
    have hnp : ∀ y ∈ (Finset.univ : Finset V), g y * π y ≤ 0 := by
      intro y _
      nlinarith [hcon y, (hpos y).le]
    have hz := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hgexp
    have hzero : MarkovMixing.innerPi π g g = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rcases mul_eq_zero.mp (hz x (Finset.mem_univ x)) with h | h
      · rw [h]; ring
      · exact absurd h (hpos x).ne'
    rw [hgnorm] at hzero
    norm_num at hzero
  obtain ⟨x1, hx1⟩ := hgexists
  have hfx1 : 0 < f x1 := lt_max_iff.mpr (Or.inl hx1)
  have hNpos : 0 < N := by
    rw [hN_def]
    show 0 < ∑ x, f x * f x * π x
    refine Finset.sum_pos' (fun i _ => mul_nonneg (mul_nonneg (hfnn i) (hfnn i)) (hpos i).le)
      ⟨x1, Finset.mem_univ x1, mul_pos (mul_pos hfx1 hfx1) (hpos x1)⟩
  -- the Dirichlet energy of f is at most γ ‖f‖²
  have hEle : E ≤ MarkovMixing.spectralGap P * N := by
    have hd : E = N - MarkovMixing.innerPi π f (P.mulVec f) := dirichlet_eq_inner hP hπ f
    have hlam : ∀ x : V, MarkovMixing.lambdaTwo P * f x ≤ (P.mulVec f) x := by
      intro x
      by_cases hx : 0 < g x
      · have hfx : f x = g x := max_eq_left (le_of_lt hx)
        have h1 : (P.mulVec g) x ≤ (P.mulVec f) x := by
          show ∑ y, P x y * g y ≤ ∑ y, P x y * f y
          exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfge y) (hP.1 x y)
        have h2 : (P.mulVec g) x = MarkovMixing.lambdaTwo P * g x := by
          rw [hgeig]; simp
        rw [hfx]
        linarith [h1, h2]
      · push_neg at hx
        have hfx : f x = 0 := max_eq_right hx
        rw [hfx, mul_zero]
        show 0 ≤ ∑ y, P x y * f y
        exact Finset.sum_nonneg fun y _ => mul_nonneg (hP.1 x y) (hfnn y)
    have hterm : MarkovMixing.lambdaTwo P * N ≤ MarkovMixing.innerPi π f (P.mulVec f) := by
      rw [hN_def]
      show MarkovMixing.lambdaTwo P * (∑ x, f x * f x * π x) ≤ ∑ x, f x * (P.mulVec f) x * π x
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 := hlam x
      have h2 : 0 ≤ f x * π x := mul_nonneg (hfnn x) (hpos x).le
      nlinarith
    have hgd : MarkovMixing.spectralGap P = 1 - MarkovMixing.lambdaTwo P := rfl
    rw [hd, hgd]
    nlinarith [hterm]
  -- the co-area inequality applied to f²
  have hfilt : (Finset.univ.filter (fun x : V => 0 < f x ^ 2))
      = Finset.univ.filter (fun x : V => 0 < g x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h1 : 0 < f x := by
        rcases (hfnn x).lt_or_eq with h2 | h2
        · exact h2
        · rw [← h2] at h; norm_num at h
      rcases lt_max_iff.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (lt_irrefl 0)
    · intro h
      have h1 : 0 < f x := lt_max_iff.mpr (Or.inl h)
      positivity
  have hdistf : MarkovMixing.distExp π (fun x => f x ^ 2) = N := by
    rw [hN_def]
    show ∑ x, f x ^ 2 * π x = ∑ x, f x * f x * π x
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcoarea := MarkovMixing.bottleneck_coarea P hP hirr π hπ hrev (fun x => f x ^ 2)
    (fun x => sq_nonneg _) (by rw [hfilt]; exact hgsupp)
  rw [hdistf] at hcoarea
  set A : ℝ := ∑ x, ∑ y, max (f x ^ 2 - f y ^ 2) 0 * MarkovMixing.edgeMeasure P π x y with hA_def
  have hcoarea' : MarkovMixing.bottleneckStar P π * N ≤ A := hcoarea
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (le_max_right _ _) (hQnn x y)
  -- Cauchy-Schwarz
  have hfact : ∀ x y : V, max (f x ^ 2 - f y ^ 2) 0
      = max (f x - f y) 0 * (if f y < f x then f x + f y else 0) := by
    intro x y
    by_cases h : f y < f x
    · rw [if_pos h, max_eq_left (show (0:ℝ) ≤ f x - f y by linarith),
        max_eq_left (show (0:ℝ) ≤ f x ^ 2 - f y ^ 2 by nlinarith [hfnn y])]
      ring
    · push_neg at h
      rw [if_neg (not_lt.mpr h), mul_zero,
        max_eq_right (show f x ^ 2 - f y ^ 2 ≤ 0 by nlinarith [hfnn x])]
  have hprod : ∀ p : V × V,
      (max (f p.1 - f p.2) 0 * (if f p.2 < f p.1 then f p.1 + f p.2 else 0)
        * MarkovMixing.edgeMeasure P π p.1 p.2) ^ 2
      ≤ ((max (f p.1 - f p.2) 0) ^ 2 * MarkovMixing.edgeMeasure P π p.1 p.2)
        * ((if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0)
            * MarkovMixing.edgeMeasure P π p.1 p.2) := by
    intro p
    by_cases h : f p.2 < f p.1
    · exact le_of_eq (by rw [if_pos h, if_pos h]; ring)
    · exact le_of_eq (by rw [if_neg h, if_neg h]; ring)
  have hite : ∀ p : V × V, 0 ≤ (if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0) := by
    intro p
    by_cases h : f p.2 < f p.1
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hCS0 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (V × V))
    (r := fun p : V × V => max (f p.1 - f p.2) 0 * (if f p.2 < f p.1 then f p.1 + f p.2 else 0)
      * MarkovMixing.edgeMeasure P π p.1 p.2)
    (f := fun p : V × V => (max (f p.1 - f p.2) 0) ^ 2 * MarkovMixing.edgeMeasure P π p.1 p.2)
    (g := fun p : V × V => (if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0)
      * MarkovMixing.edgeMeasure P π p.1 p.2)
    (fun p _ => mul_nonneg (sq_nonneg _) (hQnn p.1 p.2))
    (fun p _ => mul_nonneg (hite p) (hQnn p.1 p.2))
    (fun p _ => hprod p)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hCS0
  have hA_eq : A = ∑ x, ∑ y, max (f x - f y) 0 * (if f y < f x then f x + f y else 0)
      * MarkovMixing.edgeMeasure P π x y := by
    rw [hA_def]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hfact x y]
  have hE_eq : ∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * MarkovMixing.edgeMeasure P π x y = E :=
    pos_part_sq f hrev
  have hW_le : ∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0)
      * MarkovMixing.edgeMeasure P π x y ≤ 2 * N - E := add_part_sq_le hP hπ hrev hpos f
  rw [← hA_eq, hE_eq] at hCS0
  have hCS : A ^ 2 ≤ E * (2 * N - E) :=
    le_trans hCS0 (mul_le_mul_of_nonneg_left hW_le hEnn)
  -- final algebra
  have hΦN : 0 ≤ MarkovMixing.bottleneckStar P π * N := mul_nonneg hΦnn hNpos.le
  have hsq : (MarkovMixing.bottleneckStar P π * N) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hΦN hcoarea' 2
  have hkey : MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2 ≤ E * (2 * N - E) := by
    have e : (MarkovMixing.bottleneckStar P π * N) ^ 2
        = MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2 := by ring
    rw [e] at hsq
    linarith [hsq, hCS]
  have h1 : (1 - MarkovMixing.spectralGap P) * N ≤ N - E := by nlinarith [hEle]
  have h2 : 0 ≤ (1 - MarkovMixing.spectralGap P) * N := by nlinarith [hNpos]
  have h3 : ((1 - MarkovMixing.spectralGap P) * N) ^ 2 ≤ (N - E) ^ 2 := by nlinarith [h1, h2]
  have h6 : MarkovMixing.bottleneckStar P π ^ 2 ≤ 1 - (1 - MarkovMixing.spectralGap P) ^ 2 := by
    have hN2 : 0 < N ^ 2 := by positivity
    have h5 : MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2
        ≤ (1 - (1 - MarkovMixing.spectralGap P) ^ 2) * N ^ 2 := by nlinarith [hkey, h3]
    exact le_of_mul_le_mul_right h5 hN2
  nlinarith [h6, sq_nonneg (MarkovMixing.spectralGap P)]
