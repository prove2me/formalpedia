-- Prove2me | solution 1 for MarkovMixing.sep_le_stopping_tail
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:39:09.965389+00:00
-- url     : https://prove2.me/submissions/c619211a-4267-4507-86c2-2de1e5baa1eb

import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_stationary_unique
import Definitions.Def_mm_stopping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000

/-- Splitting a trajectory of length `n+1` into its first `n` steps and its final state. -/
private def snocEquivV (V : Type*) (n : ℕ) : ((Fin (n + 1) → V) × V) ≃ (Fin (n + 2) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (fun i => ω i.castSucc, ω (Fin.last (n + 1)))
  left_inv := by rintro ⟨q, v⟩; ext <;> simp
  right_inv := by intro ω; exact Fin.snoc_init_self ω

@[simp] private lemma snocEquivV_castSucc {V : Type*} (n : ℕ)
    (p : (Fin (n + 1) → V) × V) (i : Fin (n + 1)) :
    snocEquivV V n p i.castSucc = p.1 i := by
  simp [snocEquivV]

@[simp] private lemma snocEquivV_last {V : Type*} (n : ℕ) (p : (Fin (n + 1) → V) × V) :
    snocEquivV V n p (Fin.last (n + 1)) = p.2 := by
  simp [snocEquivV]

/-- `P_x{τ ≥ t, X_t = y}`: the trajectory has not been stopped strictly before `t`. -/
private noncomputable def Dfun {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (t : ℕ) (y : V) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y then
      pathWeight P ω * ∏ u : Fin t, (1 - s u.val (pathPrefix ω u))
    else 0

/-- `P_x{τ > t, X_t = y}`: the trajectory has not been stopped at any time `≤ t`. -/
private noncomputable def Efun {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (t : ℕ) (y : V) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y then
      pathWeight P ω * (∏ u : Fin t, (1 - s u.val (pathPrefix ω u))) * (1 - s t ω)
    else 0

/-- Splitting on whether the rule fires at time `t`. -/
private lemma Dfun_eq {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (t : ℕ) (y : V) :
    Dfun P x s t y = Efun P x s t y + stopAtProb P x s t y := by
  unfold Dfun Efun stopAtProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y
  · rw [if_pos h, if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, if_neg h]; ring

private lemma Efun_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (hs : IsStoppingRule s) (t : ℕ) (y : V) :
    0 ≤ Efun P x s t y := by
  unfold Efun
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y
  · rw [if_pos h]
    have h1 : 0 ≤ pathWeight P ω :=
      Finset.prod_nonneg fun i _ => hP.1 _ _
    have h2 : 0 ≤ ∏ u : Fin t, (1 - s u.val (pathPrefix ω u)) :=
      Finset.prod_nonneg fun u _ => by linarith [(hs u.val (pathPrefix ω u)).2]
    have h3 : 0 ≤ 1 - s t ω := by linarith [(hs t ω).2]
    positivity
  · rw [if_neg h]

/-- The one-step recursion obtained by splitting off the last step of a trajectory. -/
private lemma Dfun_succ {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (n : ℕ) (y : V) :
    Dfun P x s (n + 1) y = ∑ z, Efun P x s n z * P z y := by
  classical
  have hL : Dfun P x s (n + 1) y
      = ∑ ω : Fin (n + 2) → V,
          (if ω 0 = x ∧ ω (Fin.last (n + 1)) = y then
            pathWeight P ω * ∏ u : Fin (n + 1), (1 - s u.val (pathPrefix ω u))
          else 0) := rfl
  rw [hL, ← Equiv.sum_comp (snocEquivV V n)
    (fun ω : Fin (n + 2) → V =>
      if ω 0 = x ∧ ω (Fin.last (n + 1)) = y then
        pathWeight P ω * ∏ u : Fin (n + 1), (1 - s u.val (pathPrefix ω u))
      else 0)]
  have hstep : ∀ p : (Fin (n + 1) → V) × V,
      (if (snocEquivV V n p) 0 = x ∧ (snocEquivV V n p) (Fin.last (n + 1)) = y then
        pathWeight P (snocEquivV V n p) *
          ∏ u : Fin (n + 1), (1 - s u.val (pathPrefix (snocEquivV V n p) u))
      else 0)
      = (if p.1 0 = x ∧ p.2 = y then
          (pathWeight P p.1 * (∏ u : Fin n, (1 - s u.val (pathPrefix p.1 u))) *
            (1 - s n p.1)) * P (p.1 (Fin.last n)) p.2
        else 0) := by
    intro p
    have hrestrict : ∀ i : Fin (n + 1), (snocEquivV V n p) i.castSucc = p.1 i :=
      fun i => snocEquivV_castSucc n p i
    have hlast : (snocEquivV V n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
    have hzero : (snocEquivV V n p) 0 = p.1 0 := by
      have h := hrestrict 0
      rwa [Fin.castSucc_zero] at h
    have hpref_last : pathPrefix (snocEquivV V n p) (Fin.last n) = p.1 := by
      funext i
      exact hrestrict i
    have hpref : ∀ u : Fin n,
        pathPrefix (snocEquivV V n p) u.castSucc = pathPrefix p.1 u := by
      intro u
      funext i
      exact hrestrict ⟨i.val, by have := i.isLt; have := u.isLt; omega⟩
    have hprod : (∏ u : Fin (n + 1), (1 - s u.val (pathPrefix (snocEquivV V n p) u)))
        = (∏ u : Fin n, (1 - s u.val (pathPrefix p.1 u))) * (1 - s n p.1) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun u _ => ?_
        exact congrArg (fun w : Fin ((u : ℕ) + 1) → V => 1 - s (u : ℕ) w) (hpref u)
      · exact congrArg (fun w : Fin (n + 1) → V => 1 - s n w) hpref_last
    have hweight : pathWeight P (snocEquivV V n p)
        = pathWeight P p.1 * P (p.1 (Fin.last n)) p.2 := by
      have hpw : pathWeight P (snocEquivV V n p)
          = ∏ i : Fin (n + 1),
              P ((snocEquivV V n p) i.castSucc) ((snocEquivV V n p) i.succ) := rfl
      rw [hpw, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hrestrict i.castSucc]
        congr 1
        exact hrestrict i.succ
      · rw [hrestrict (Fin.last n)]
        congr 1
    rw [hzero, hlast, hprod, hweight]
    by_cases h : p.1 0 = x ∧ p.2 = y
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
  have hinner : ∀ ω : Fin (n + 1) → V,
      (∑ v : V, if ω 0 = x ∧ v = y then
          (pathWeight P ω * (∏ u : Fin n, (1 - s u.val (pathPrefix ω u))) *
            (1 - s n ω)) * P (ω (Fin.last n)) v else 0)
      = (if ω 0 = x then
          (pathWeight P ω * (∏ u : Fin n, (1 - s u.val (pathPrefix ω u))) *
            (1 - s n ω)) * P (ω (Fin.last n)) y else 0) := by
    intro ω
    by_cases h : ω 0 = x
    · rw [if_pos h, Finset.sum_eq_single y]
      · rw [if_pos ⟨h, rfl⟩]
      · intro v _ hv
        rw [if_neg (fun hc => hv hc.2)]
      · intro hc; exact absurd (Finset.mem_univ y) hc
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
  rw [Finset.sum_congr rfl fun ω _ => hinner ω]
  -- now expand the right-hand side the same way
  have hR : ∑ z, Efun P x s n z * P z y
      = ∑ z, ∑ ω : Fin (n + 1) → V,
          (if ω 0 = x ∧ ω (Fin.last n) = z then
            (pathWeight P ω * (∏ u : Fin n, (1 - s u.val (pathPrefix ω u))) *
              (1 - s n ω)) * P z y else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold Efun
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω 0 = x ∧ ω (Fin.last n) = z
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = x
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last n))]
    · rw [if_pos ⟨h, rfl⟩]
    · intro z _ hz
      rw [if_neg]
      rintro ⟨-, hlz⟩
      exact hz hlz.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun z _ => by rw [if_neg (fun hc => h hc.1)]).symm

private lemma Dfun_zero {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (y : V) :
    Dfun P x s 0 y = if x = y then 1 else 0 := by
  classical
  have hL : Dfun P x s 0 y
      = ∑ ω : Fin 1 → V, (if ω 0 = x ∧ ω 0 = y then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hcond : (ω 0 = x ∧ ω (Fin.last 0) = y) ↔ (ω 0 = x ∧ ω 0 = y) := by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
    by_cases h : ω 0 = x ∧ ω 0 = y
    · rw [if_pos (hcond.mpr h), if_pos h]
      simp [pathWeight]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [hL]
  by_cases hxy : x = y
  · rw [if_pos hxy, Finset.sum_eq_single (fun _ : Fin 1 => x)]
    · rw [if_pos ⟨rfl, hxy⟩]
    · intro ω _ hne
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hne (funext fun i => by rw [Subsingleton.elim i 0, h1])
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hxy (h1.symm.trans h2)

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (x : V)
    (hs : IsStrongStationaryTime P π x s) (t : ℕ) :
    sepDist P π x t ≤ stopTailProb P x s t := by
  classical
  haveI : Nonempty V := ⟨x⟩
  obtain ⟨hrule, -, hstrong⟩ := hs
  -- positivity of the stationary distribution
  obtain ⟨π', hst', hpos', -⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  have hππ : π = π' := MarkovMixing.stationary_unique P hP hirr π π' hπ hst'
  have hpos : ∀ y : V, 0 < π y := by
    intro y; rw [hππ]; exact hpos' y
  have hstat : ∀ y : V, ∑ z, π z * P z y = π y := fun y => congrFun hπ.2 y
  -- the exact decomposition of `P^t(x,y)`
  have hmain : ∀ (n : ℕ) (y : V),
      (P ^ n) x y
        = π y * (∑ u ∈ Finset.range (n + 1), ∑ z, stopAtProb P x s u z)
          + Efun P x s n y := by
    intro n
    induction n with
    | zero =>
        intro y
        have h0 : (P ^ 0) x y = if x = y then (1 : ℝ) else 0 := by
          rw [pow_zero, Matrix.one_apply]
        rw [h0, ← Dfun_zero P x s y, Dfun_eq P x s 0 y, hstrong 0 y]
        simp
        ring
    | succ n ih =>
        intro y
        have hpow : (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by
          rw [pow_succ]
          rfl
        rw [hpow, Finset.sum_congr rfl fun z _ => by rw [ih z]]
        have hsplit : ∑ z, (π z * (∑ u ∈ Finset.range (n + 1), ∑ w, stopAtProb P x s u w)
              + Efun P x s n z) * P z y
            = (∑ u ∈ Finset.range (n + 1), ∑ w, stopAtProb P x s u w) * (∑ z, π z * P z y)
              + ∑ z, Efun P x s n z * P z y := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
        have hrange : ∑ u ∈ Finset.range (n + 1 + 1), ∑ z, stopAtProb P x s u z
            = (∑ u ∈ Finset.range (n + 1), ∑ z, stopAtProb P x s u z)
              + ∑ z, stopAtProb P x s (n + 1) z := Finset.sum_range_succ _ _
        rw [hsplit, hstat y, ← Dfun_succ P x s n y, Dfun_eq P x s (n + 1) y,
          hstrong (n + 1) y, hrange]
        ring
  -- conclude
  have hbound : ∀ y : V, 1 - (P ^ t) x y / π y ≤ stopTailProb P x s t := by
    intro y
    have hy := hmain t y
    have hE : 0 ≤ Efun P x s t y := Efun_nonneg P hP x s hrule t y
    have hπy : 0 < π y := hpos y
    have hdiv : (∑ u ∈ Finset.range (t + 1), ∑ z, stopAtProb P x s u z)
        ≤ (P ^ t) x y / π y := by
      rw [le_div_iff₀ hπy]
      nlinarith [hy, hE]
    unfold stopTailProb
    linarith [hdiv]
  exact ciSup_le hbound
