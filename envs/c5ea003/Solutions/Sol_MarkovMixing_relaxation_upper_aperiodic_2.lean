-- Prove2me | solution 2 for MarkovMixing.relaxation_upper_aperiodic
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T17:24:39.131375+00:00
-- url     : https://prove2.me/submissions/c7421205-af1c-44f3-883b-163a2a75a7e5

import Theorems.Thm_MarkovMixing_spectral_representation
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_stationary_unique
import Definitions.Def_mm_spectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators
open scoped Matrix
open MarkovMixing

set_option maxHeartbeats 1000000

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime P π ε : ℝ) ≤
      Real.log (1 / (ε * ⨅ x : V, π x)) * relaxationTime P + 1 := by
  classical
  -- (0) the stationary distribution is positive
  obtain ⟨π', hst', hpos', -⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  have hππ : π = π' := MarkovMixing.stationary_unique P hP hirr π π' hπ hst'
  have hpos : ∀ x : V, 0 < π x := fun x => by rw [hππ]; exact hpos' x
  have hπsum : ∑ x, π x = 1 := hπ.1.2
  have hπne : ∀ x : V, π x ≠ 0 := fun x => ne_of_gt (hpos x)
  -- (1) the spectral data
  obtain ⟨lam, f, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hbasic := MarkovMixing.eigenvalue_basic P hP
  -- (2) completeness, read off the spectral decomposition at `t = 0`
  have hcomp : ∀ x y : V, ∑ j, f j x * f j y = if x = y then 1 / π y else 0 := by
    intro x y
    have h := hspec 0 x y
    rw [pow_zero, Matrix.one_apply] at h
    have h2 : ∑ j, f j x * f j y = (if x = y then (1 : ℝ) else 0) / π y := by
      rw [h]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_zero, mul_one]
    rw [h2]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy]
    · rw [if_neg hxy, if_neg hxy, zero_div]
  have hsq : ∀ x : V, ∑ j, f j x ^ 2 = 1 / π x := by
    intro x
    have h := hcomp x x
    rw [if_pos rfl] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- (3) eigenfunctions of eigenvalue `1` are the normalised constants
  have hev : ∀ j, IsEigenvalue P (lam j) := by
    intro j
    refine ⟨f j, ?_, heig j⟩
    intro hzero
    have h := horth j j
    rw [if_pos rfl] at h
    unfold innerPi at h
    rw [hzero] at h
    simp at h
  have hconst : ∀ j, lam j = 1 → ∀ x y : V, f j x = f j y := by
    intro j hj x y
    have hPf : P.mulVec (f j) = f j := by rw [heig j, hj, one_smul]
    exact hbasic.2.1 hirr (f j) hPf x y
  have hone : ∀ j, lam j = 1 → ∀ x : V, f j x ^ 2 = 1 := by
    intro j hj x
    have h := horth j j
    rw [if_pos rfl] at h
    unfold innerPi at h
    have hrw : ∑ y, f j y * f j y * π y = f j x ^ 2 * ∑ y, π y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [hconst j hj y x]; ring
    rw [hrw, hπsum, mul_one] at h
    exact h
  have hTcard : (Finset.univ.filter (fun j => lam j = 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro j hj k hk
    by_contra hjk
    have hj1 : lam j = 1 := (Finset.mem_filter.mp hj).2
    have hk1 : lam k = 1 := (Finset.mem_filter.mp hk).2
    have h := horth j k
    rw [if_neg hjk] at h
    obtain ⟨x⟩ := ‹Nonempty V›
    have hval : innerPi π (f j) (f k) = f j x * f k x := by
      unfold innerPi
      rw [← mul_one (f j x * f k x), ← hπsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        rw [hconst j hj1 y x, hconst k hk1 y x]
    rw [hval] at h
    have hsq2 : (f j x * f k x) ^ 2 = 1 := by
      rw [mul_pow, hone j hj1 x, hone k hk1 x]; ring
    rw [h] at hsq2
    norm_num at hsq2
  -- (4) every eigenvalue occurs among the `lam j`
  have hsumdiv : ∀ (u : V → ℝ) (d : ℝ), ∑ y, u y / d = (∑ y, u y) / d := by
    intro u d
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hexpandf : ∀ (g : V → ℝ) (y : V), ∑ j, innerPi π (f j) g * f j y = g y := by
    intro g y
    have h1 : ∀ j, innerPi π (f j) g * f j y
        = ∑ w, (g w * π w) * (f j w * f j y) := by
      intro j
      unfold innerPi
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
    have h2 : ∀ w : V, ∑ j, (g w * π w) * (f j w * f j y)
        = (g w * π w) * (if w = y then 1 / π y else 0) := by
      intro w
      rw [← Finset.mul_sum, hcomp w y]
    rw [Finset.sum_congr rfl fun w _ => h2 w, Finset.sum_eq_single y]
    · rw [if_pos rfl, mul_one_div, mul_div_assoc, div_self (hπne y), mul_one]
    · intro w _ hw
      rw [if_neg hw, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ y) hc
  have hselfadj : ∀ (j : Fin (Fintype.card V)) (g : V → ℝ),
      innerPi π (f j) (P.mulVec g) = lam j * innerPi π (f j) g := by
    intro j g
    have hfj : ∀ z : V, ∑ y, P z y * f j y = lam j * f j z := by
      intro z
      have h := congrFun (heig j) z
      simpa [Matrix.mulVec, dotProduct] using h
    have hstep : ∀ y : V, f j y * (P.mulVec g) y * π y
        = ∑ z, (f j y * π y) * (P y z * g z) := by
      intro y
      show f j y * (∑ z, P y z * g z) * π y = _
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ => by ring
    unfold innerPi
    rw [Finset.sum_congr rfl fun y _ => hstep y, Finset.sum_comm]
    have hinner : ∀ z : V, ∑ y, (f j y * π y) * (P y z * g z)
        = lam j * (f j z * g z * π z) := by
      intro z
      have h1 : ∀ y : V, (f j y * π y) * (P y z * g z) = (g z * π z) * (P z y * f j y) := by
        intro y
        linear_combination (f j y * g z) * hrev y z
      rw [Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum, hfj z]
      ring
    rw [Finset.sum_congr rfl fun z _ => hinner z, ← Finset.mul_sum]
  have hallev : ∀ l : ℝ, IsEigenvalue P l → ∃ j, l = lam j := by
    rintro l ⟨g, hg0, hgl⟩
    by_contra hc
    push Not at hc
    have hcoef : ∀ j, innerPi π (f j) g = 0 := by
      intro j
      have h1 : innerPi π (f j) (P.mulVec g) = lam j * innerPi π (f j) g := hselfadj j g
      have h2 : innerPi π (f j) (P.mulVec g) = l * innerPi π (f j) g := by
        rw [hgl]
        unfold innerPi
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        show f j y * (l * g y) * π y = l * (f j y * g y * π y)
        ring
      have h3 : (l - lam j) * innerPi π (f j) g = 0 := by
        have := h1.symm.trans h2
        linarith [this]
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd (by linarith [h] : l = lam j) (hc j)
      · exact h
    have hg : ∀ y : V, g y = 0 := by
      intro y
      rw [← hexpandf g y]
      exact Finset.sum_eq_zero fun j _ => by rw [hcoef j, zero_mul]
    exact hg0 (funext fun y => by rw [hg y]; rfl)
  -- (5) the absolute spectral gap is positive
  have hbdd : BddAbove {r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨l, hl, -, rfl⟩
    exact hbasic.1 l hl
  have hstar_le : ∀ j, lam j ≠ 1 → |lam j| ≤ lambdaStar P := by
    intro j hj
    exact le_csSup hbdd ⟨lam j, hev j, hj, rfl⟩
  have hstar_nonneg : 0 ≤ lambdaStar P := by
    unfold lambdaStar
    refine Real.sSup_nonneg ?_
    rintro r ⟨l, -, -, rfl⟩
    exact abs_nonneg l
  haveI : Nonempty (Fin (Fintype.card V)) := ⟨⟨0, Fintype.card_pos⟩⟩
  have hunivne : (Finset.univ : Finset (Fin (Fintype.card V))).Nonempty := Finset.univ_nonempty
  have hlamlt : ∀ j, lam j ≠ 1 → |lam j| < 1 := by
    intro j hj
    have h1 : |lam j| ≤ 1 := hbasic.1 _ (hev j)
    have h2 : lam j ≠ -1 := by
      intro hcc
      exact (hbasic.2.2 hirr hap) (by rw [← hcc]; exact hev j)
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h' | h'
      · exact hj h'
      · exact h2 h'
  set gmax : ℝ :=
    Finset.univ.sup' hunivne (fun j => if lam j = 1 then (0 : ℝ) else |lam j|) with hgmaxdef
  have hgmaxlt : gmax < 1 := by
    rw [hgmaxdef, Finset.sup'_lt_iff]
    intro j _
    by_cases hj : lam j = 1
    · rw [if_pos hj]; norm_num
    · rw [if_neg hj]; exact hlamlt j hj
  have hgmax_nonneg : 0 ≤ gmax := by
    obtain ⟨j0⟩ := ‹Nonempty (Fin (Fintype.card V))›
    have hle : (if lam j0 = 1 then (0 : ℝ) else |lam j0|) ≤ gmax := by
      rw [hgmaxdef]
      exact Finset.le_sup' (fun j => if lam j = 1 then (0 : ℝ) else |lam j|)
        (Finset.mem_univ j0)
    by_cases hj : lam j0 = 1
    · rw [if_pos hj] at hle; exact hle
    · rw [if_neg hj] at hle; exact le_trans (abs_nonneg _) hle
  have hstar_lt : lambdaStar P < 1 := by
    have hle : lambdaStar P ≤ gmax := by
      unfold lambdaStar
      refine Real.sSup_le ?_ hgmax_nonneg
      rintro r ⟨l, hl, hl1, rfl⟩
      obtain ⟨j, hj⟩ := hallev l hl
      subst hj
      have hle2 : (if lam j = 1 then (0 : ℝ) else |lam j|) ≤ gmax := by
        rw [hgmaxdef]
        exact Finset.le_sup' (fun j => if lam j = 1 then (0 : ℝ) else |lam j|)
          (Finset.mem_univ j)
      rw [if_neg hl1] at hle2
      exact hle2
    linarith
  -- (6) elementary facts about the powers of `P`
  have hpownn : ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
    intro t
    induction t with
    | zero => intro x y; by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
    | succ n ih =>
        intro x y
        have h : (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by rw [pow_succ]; rfl
        rw [h]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)
  have hrowsum : ∀ (t : ℕ) (x : V), ∑ y, (P ^ t) x y = 1 := by
    intro t
    induction t with
    | zero => intro x; simp [Matrix.one_apply]
    | succ n ih =>
        intro x
        have h : ∀ y : V, (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by
          intro y; rw [pow_succ]; rfl
        rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_comm]
        have h2 : ∀ z : V, ∑ y, (P ^ n) x z * P z y = (P ^ n) x z := by
          intro z; rw [← Finset.mul_sum, hP.2 z, mul_one]
        rw [Finset.sum_congr rfl fun z _ => h2 z, ih x]
  have hrevpow : ∀ (t : ℕ) (x y : V), π x * (P ^ t) x y = π y * (P ^ t) y x := by
    intro t
    induction t with
    | zero =>
        intro x y
        rw [pow_zero, Matrix.one_apply, Matrix.one_apply]
        by_cases hxy : x = y
        · rw [if_pos hxy, if_pos hxy.symm, hxy]
        · rw [if_neg hxy, if_neg (Ne.symm hxy)]; ring
    | succ n ih =>
        intro x y
        have hL : (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by rw [pow_succ]; rfl
        have hR : (P ^ (n + 1)) y x = ∑ z, P y z * (P ^ n) z x := by rw [pow_succ']; rfl
        rw [hL, hR, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        have h1 : π x * ((P ^ n) x z * P z y) = (π x * (P ^ n) x z) * P z y := by ring
        rw [h1, ih x z]
        have h2 : π z * P z y = π y * P y z := hrev z y
        linear_combination ((P ^ n) z x) * h2
  -- (7) the chi-square bound
  have hchi : ∀ (t : ℕ) (x : V),
      ∑ y, ((P ^ t) x y - π y) ^ 2 / π y = (∑ j, f j x ^ 2 * lam j ^ (2 * t)) - 1 := by
    intro t x
    have hexpand : ∀ y : V, ((P ^ t) x y - π y) ^ 2 / π y
        = ((P ^ t) x y) ^ 2 / π y - 2 * (P ^ t) x y + π y := by
      intro y
      have hy : π y ≠ 0 := hπne y
      field_simp
      ring
    have hkey : ∑ y, ((P ^ t) x y) ^ 2 / π y = ∑ j, f j x ^ 2 * lam j ^ (2 * t) := by
      have hdiv : ∀ y : V, ((P ^ t) x y) ^ 2 / π y = (P ^ t) x y * (P ^ t) y x / π x := by
        intro y
        have h := hrevpow t x y
        have hy : π y ≠ 0 := hπne y
        have hx : π x ≠ 0 := hπne x
        field_simp
        linear_combination ((P ^ t) x y) * h
      rw [Finset.sum_congr rfl fun y _ => hdiv y, hsumdiv]
      have h2t : (P ^ (2 * t)) x x = ∑ y, (P ^ t) x y * (P ^ t) y x := by
        rw [two_mul, pow_add]; rfl
      rw [← h2t, hspec (2 * t) x x]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun y _ => hexpand y, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hrowsum t x, hπsum, hkey]
    ring
  -- (8) Cauchy–Schwarz: total variation is controlled by the chi-square distance
  have htv : ∀ (t : ℕ) (x : V),
      4 * (tvDist (rowDist P t x) π) ^ 2 ≤ ∑ y, ((P ^ t) x y - π y) ^ 2 / π y := by
    intro t x
    have hdist : IsDist (rowDist P t x) := ⟨fun y => hpownn t x y, hrowsum t x⟩
    have htveq := (MarkovMixing.tv_eq_half_l1 (rowDist P t x) π hdist hπ.1).1
    have hsqrtpos : ∀ y : V, 0 < Real.sqrt (π y) := fun y => Real.sqrt_pos.mpr (hpos y)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
      (fun y => |(P ^ t) x y - π y| / Real.sqrt (π y)) (fun y => Real.sqrt (π y))
    have hfg : ∀ y : V, (|(P ^ t) x y - π y| / Real.sqrt (π y)) * Real.sqrt (π y)
        = |(P ^ t) x y - π y| := fun y => div_mul_cancel₀ _ (ne_of_gt (hsqrtpos y))
    have hf2 : ∀ y : V, (|(P ^ t) x y - π y| / Real.sqrt (π y)) ^ 2
        = ((P ^ t) x y - π y) ^ 2 / π y := by
      intro y
      rw [div_pow, sq_abs, Real.sq_sqrt (le_of_lt (hpos y))]
    have hg2 : ∀ y : V, (Real.sqrt (π y)) ^ 2 = π y :=
      fun y => Real.sq_sqrt (le_of_lt (hpos y))
    rw [Finset.sum_congr rfl fun y _ => hfg y, Finset.sum_congr rfl fun y _ => hf2 y,
      Finset.sum_congr rfl fun y _ => hg2 y, hπsum, mul_one] at hcs
    have hrw : ∀ y : V, |rowDist P t x y - π y| = |(P ^ t) x y - π y| := fun y => rfl
    rw [htveq, Finset.sum_congr rfl fun y _ => hrw y]
    nlinarith [hcs]
  -- (9) the spectral bound
  have hbound : ∀ (t : ℕ) (x : V),
      4 * (tvDist (rowDist P t x) π) ^ 2 ≤ (lambdaStar P) ^ (2 * t) / π x := by
    intro t x
    refine le_trans (htv t x) ?_
    rw [hchi t x]
    have hsplit : ∑ j, f j x ^ 2 * lam j ^ (2 * t)
        = (∑ j ∈ Finset.univ.filter (fun j => lam j = 1), f j x ^ 2 * lam j ^ (2 * t))
          + ∑ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ, f j x ^ 2 * lam j ^ (2 * t) := by
      rw [Finset.sum_add_sum_compl]
    have hT1 : (∑ j ∈ Finset.univ.filter (fun j => lam j = 1), f j x ^ 2 * lam j ^ (2 * t))
        ≤ 1 := by
      have hterm : ∀ j ∈ Finset.univ.filter (fun j => lam j = 1),
          f j x ^ 2 * lam j ^ (2 * t) = 1 := by
        intro j hj
        have h1 : lam j = 1 := (Finset.mem_filter.mp hj).2
        rw [h1, one_pow, hone j h1 x, mul_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hTcard
    have hT2 : (∑ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ, f j x ^ 2 * lam j ^ (2 * t))
        ≤ (lambdaStar P) ^ (2 * t) * (1 / π x) := by
      have hstep : ∀ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ,
          f j x ^ 2 * lam j ^ (2 * t) ≤ f j x ^ 2 * (lambdaStar P) ^ (2 * t) := by
        intro j hj
        have hj1 : lam j ≠ 1 := by
          intro hcc
          exact (Finset.mem_compl.mp hj) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcc⟩)
        have habs : |lam j| ≤ lambdaStar P := hstar_le j hj1
        have hsq2 : lam j ^ 2 ≤ (lambdaStar P) ^ 2 := by
          nlinarith [habs, hstar_nonneg, sq_abs (lam j), abs_nonneg (lam j)]
        have hpow : lam j ^ (2 * t) ≤ (lambdaStar P) ^ (2 * t) := by
          calc lam j ^ (2 * t) = (lam j ^ 2) ^ t := by rw [pow_mul]
            _ ≤ ((lambdaStar P) ^ 2) ^ t := pow_le_pow_left₀ (sq_nonneg _) hsq2 t
            _ = (lambdaStar P) ^ (2 * t) := by rw [pow_mul]
        exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
      calc (∑ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ, f j x ^ 2 * lam j ^ (2 * t))
          ≤ ∑ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ,
              f j x ^ 2 * (lambdaStar P) ^ (2 * t) := Finset.sum_le_sum hstep
        _ = (∑ j ∈ (Finset.univ.filter (fun j => lam j = 1))ᶜ, f j x ^ 2)
              * (lambdaStar P) ^ (2 * t) := by rw [Finset.sum_mul]
        _ ≤ (∑ j, f j x ^ 2) * (lambdaStar P) ^ (2 * t) := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hstar_nonneg _)
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun j _ _ => sq_nonneg _)
        _ = (lambdaStar P) ^ (2 * t) * (1 / π x) := by rw [hsq x]; ring
    have hfinal : (lambdaStar P) ^ (2 * t) * (1 / π x) = (lambdaStar P) ^ (2 * t) / π x := by
      ring
    rw [hsplit]
    linarith [hT1, hT2, hfinal]
  -- (10) the relaxation time and the minimum of `π`
  have hgap : 0 < 1 - lambdaStar P := by linarith
  have htrel : relaxationTime P = (1 - lambdaStar P)⁻¹ := rfl
  have htrelpos : 0 < relaxationTime P := by rw [htrel]; exact inv_pos.mpr hgap
  have hbddb : BddBelow (Set.range π) := Set.Finite.bddBelow (Set.range π).toFinite
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) π
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hpimin_eq : (⨅ x : V, π x) = π x0 :=
    le_antisymm (ciInf_le hbddb x0) (le_ciInf fun x => hx0 x (Finset.mem_univ x))
  have hpiminpos : 0 < ⨅ x : V, π x := by rw [hpimin_eq]; exact hpos x0
  have hpimin_le : ∀ x : V, (⨅ x : V, π x) ≤ π x := fun x => ciInf_le hbddb x
  have hpimin_le1 : (⨅ x : V, π x) ≤ 1 := by
    have h : π x0 ≤ 1 := by
      have h2 := Finset.single_le_sum (f := π) (fun y _ => le_of_lt (hpos y))
        (Finset.mem_univ x0)
      rw [hπsum] at h2
      exact h2
    rw [hpimin_eq]
    exact h
  have hepimin : 0 < ε * ⨅ x : V, π x := mul_pos hε hpiminpos
  set L : ℝ := Real.log (1 / (ε * ⨅ x : V, π x)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hepimin, one_mul]
    nlinarith [hpimin_le1, hpiminpos, hε1, hε]
  set t0 : ℕ := ⌈L * relaxationTime P⌉₊ with ht0def
  have ht0ge : L * relaxationTime P ≤ (t0 : ℝ) := Nat.le_ceil _
  have ht0le : (t0 : ℝ) ≤ L * relaxationTime P + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (mul_nonneg (le_of_lt hLpos) (le_of_lt htrelpos)))
  -- (11) the geometric decay
  have hexpL : Real.exp (-L) = ε * ⨅ x : V, π x := by
    rw [hLdef, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hlamexp : lambdaStar P ≤ Real.exp (-(1 - lambdaStar P)) := by
    have h := Real.add_one_le_exp (-(1 - lambdaStar P))
    linarith
  have hpowle : (lambdaStar P) ^ t0 ≤ ε * ⨅ x : V, π x := by
    have h1 : (lambdaStar P) ^ t0 ≤ (Real.exp (-(1 - lambdaStar P))) ^ t0 :=
      pow_le_pow_left₀ hstar_nonneg hlamexp t0
    have h2 : (Real.exp (-(1 - lambdaStar P))) ^ t0
        = Real.exp (-((t0 : ℝ) * (1 - lambdaStar P))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h3 : L ≤ (t0 : ℝ) * (1 - lambdaStar P) := by
      have h4 : L * (1 - lambdaStar P)⁻¹ ≤ (t0 : ℝ) := by rw [htrel] at ht0ge; exact ht0ge
      have h5 := mul_le_mul_of_nonneg_right h4 (le_of_lt hgap)
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hgap), mul_one] at h5
      exact h5
    calc (lambdaStar P) ^ t0 ≤ Real.exp (-((t0 : ℝ) * (1 - lambdaStar P))) := by
          rw [← h2]; exact h1
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = ε * ⨅ x : V, π x := hexpL
  -- (12) the mixing bound
  have hdle : distStationary P π t0 ≤ ε := by
    refine ciSup_le fun x => ?_
    have h4 := hbound t0 x
    have hpow2 : (lambdaStar P) ^ (2 * t0) = ((lambdaStar P) ^ t0) ^ 2 := by
      rw [← pow_mul, mul_comm]
    rw [hpow2] at h4
    have hnn : 0 ≤ (lambdaStar P) ^ t0 := pow_nonneg hstar_nonneg t0
    have hnum : ((lambdaStar P) ^ t0) ^ 2 ≤ (ε * ⨅ x : V, π x) ^ 2 := by
      nlinarith [hpowle, hnn, hepimin]
    have hpx : 0 < π x := hpos x
    have hchain : ((lambdaStar P) ^ t0) ^ 2 / π x ≤ ε ^ 2 := by
      rw [div_le_iff₀ hpx]
      calc ((lambdaStar P) ^ t0) ^ 2 ≤ (ε * ⨅ x : V, π x) ^ 2 := hnum
        _ = ε ^ 2 * (⨅ x : V, π x) * (⨅ x : V, π x) := by ring
        _ ≤ ε ^ 2 * (⨅ x : V, π x) * 1 := by
              nlinarith [hpimin_le1, hpiminpos, sq_nonneg ε]
        _ ≤ ε ^ 2 * π x := by nlinarith [hpimin_le x, sq_nonneg ε]
    have hd : 4 * (tvDist (rowDist P t0 x) π) ^ 2 ≤ ε ^ 2 := le_trans h4 hchain
    by_contra hcon
    push Not at hcon
    nlinarith [hd, hε, hcon]
  have hms : mixingTime P π ε ≤ t0 :=
    Nat.sInf_le (show distStationary P π t0 ≤ ε from hdle)
  calc (mixingTime P π ε : ℝ) ≤ (t0 : ℝ) := by exact_mod_cast hms
    _ ≤ L * relaxationTime P + 1 := ht0le
