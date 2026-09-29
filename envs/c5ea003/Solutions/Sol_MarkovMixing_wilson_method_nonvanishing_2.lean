-- Prove2me | solution 2 for MarkovMixing.wilson_method_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T17:38:25.019223+00:00
-- url     : https://prove2.me/submissions/a7d8e832-2efe-44f6-9f83-2341e3f3386f

import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Theorems.Thm_MarkovMixing_convergence_theorem
import Definitions.Def_mm_lower
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

/-- The second-moment (distinguishing statistic) inequality: a statistic separating the
means of two distributions forces them to be far apart in total variation. -/
private lemma tv_second_moment {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (g : V → ℝ) :
    (distExp μ g - distExp ν g) ^ 2 * (1 - tvDist μ ν)
      ≤ 2 * tvDist μ ν * (distVar μ g + distVar ν g) := by
  classical
  set mμ : ℝ := distExp μ g with hmμ
  set mν : ℝ := distExp ν g with hmν
  set c : ℝ := (mμ + mν) / 2 with hc
  set Δ : ℝ := mμ - mν with hΔ
  set d : ℝ := tvDist μ ν with hd
  have hdval : d = 2⁻¹ * ∑ x, |μ x - ν x| := (MarkovMixing.tv_eq_half_l1 μ ν hμ hν).1
  have hsum : ∑ x, |μ x - ν x| = 2 * d := by rw [hdval]; ring
  -- the shifted second moment of a distribution
  have hshift : ∀ (ρ : V → ℝ), IsDist ρ →
      ∑ x, (g x - c) ^ 2 * ρ x = distVar ρ g + (distExp ρ g - c) ^ 2 := by
    intro ρ hρ
    have hexp : ∀ x : V, (g x - c) ^ 2 * ρ x
        = (g x - distExp ρ g) ^ 2 * ρ x
          + 2 * (distExp ρ g - c) * ((g x - distExp ρ g) * ρ x)
          + (distExp ρ g - c) ^ 2 * ρ x := by
      intro x; ring
    have hzero : ∑ x, (g x - distExp ρ g) * ρ x = 0 := by
      have h1 : ∑ x, (g x - distExp ρ g) * ρ x
          = (∑ x, g x * ρ x) - distExp ρ g * ∑ x, ρ x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [h1, hρ.2, mul_one]
      unfold distExp
      ring
    have hA : ∑ x, (g x - distExp ρ g) ^ 2 * ρ x = distVar ρ g := rfl
    have hB : ∑ x, 2 * (distExp ρ g - c) * ((g x - distExp ρ g) * ρ x) = 0 := by
      rw [← Finset.mul_sum, hzero, mul_zero]
    have hC : ∑ x, (distExp ρ g - c) ^ 2 * ρ x = (distExp ρ g - c) ^ 2 := by
      rw [← Finset.mul_sum, hρ.2, mul_one]
    rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hA, hB, hC, add_zero]
  -- the mean difference, recentred
  have hΔeq : Δ = ∑ x, (g x - c) * (μ x - ν x) := by
    have hterm : ∀ x : V, (g x - c) * (μ x - ν x)
        = g x * μ x - g x * ν x - c * μ x + c * ν x := fun x => by ring
    have h1 : ∑ x, (g x - c) * (μ x - ν x)
        = (∑ x, g x * μ x) - (∑ x, g x * ν x) - c * ((∑ x, μ x) - ∑ x, ν x) := by
      rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [h1, hμ.2, hν.2, sub_self, mul_zero, sub_zero, hΔ, hmμ, hmν]
    rfl
  -- Cauchy–Schwarz
  have habs : |Δ| ≤ ∑ x, |g x - c| * |μ x - ν x| := by
    rw [hΔeq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun x _ => abs_mul _ _)
  have hcs : (∑ x, |g x - c| * |μ x - ν x|) ^ 2
      ≤ (∑ x, (g x - c) ^ 2 * |μ x - ν x|) * (2 * d) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
      (fun x => |g x - c| * Real.sqrt |μ x - ν x|) (fun x => Real.sqrt |μ x - ν x|)
    have h1 : ∀ x : V, (|g x - c| * Real.sqrt |μ x - ν x|) * Real.sqrt |μ x - ν x|
        = |g x - c| * |μ x - ν x| := by
      intro x
      rw [mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have h2 : ∀ x : V, (|g x - c| * Real.sqrt |μ x - ν x|) ^ 2
        = (g x - c) ^ 2 * |μ x - ν x| := by
      intro x
      rw [mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]
    have h3 : ∀ x : V, (Real.sqrt |μ x - ν x|) ^ 2 = |μ x - ν x| :=
      fun x => Real.sq_sqrt (abs_nonneg _)
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_congr rfl fun x _ => h2 x,
      Finset.sum_congr rfl fun x _ => h3 x, hsum] at h
    exact h
  -- the weight `|μ - ν|` is dominated by `μ + ν`
  have hmc : (mμ - c) ^ 2 = Δ ^ 2 / 4 := by rw [hc, hΔ]; ring
  have hnc : (mν - c) ^ 2 = Δ ^ 2 / 4 := by rw [hc, hΔ]; ring
  have hdom : ∑ x, (g x - c) ^ 2 * |μ x - ν x|
      ≤ (distVar μ g + Δ ^ 2 / 4) + (distVar ν g + Δ ^ 2 / 4) := by
    have hstep : ∑ x, (g x - c) ^ 2 * |μ x - ν x|
        ≤ ∑ x, ((g x - c) ^ 2 * μ x + (g x - c) ^ 2 * ν x) := by
      refine Finset.sum_le_sum fun x _ => ?_
      have habs2 : |μ x - ν x| ≤ μ x + ν x := by
        rcases abs_cases (μ x - ν x) with ⟨h, -⟩ | ⟨h, -⟩ <;>
          [linarith [hν.1 x, h]; linarith [hμ.1 x, h]]
      nlinarith [sq_nonneg (g x - c), habs2]
    refine le_trans hstep ?_
    rw [Finset.sum_add_distrib, hshift μ hμ, hshift ν hν, hmc, hnc]
  -- combine
  have hdnn : 0 ≤ d := by
    rw [hdval]
    have : (0 : ℝ) ≤ ∑ x, |μ x - ν x| := Finset.sum_nonneg fun x _ => abs_nonneg _
    linarith
  have hsq : Δ ^ 2 ≤ (∑ x, |g x - c| * |μ x - ν x|) ^ 2 := by
    have h1 : |Δ| ^ 2 = Δ ^ 2 := sq_abs Δ
    have h2 : (0 : ℝ) ≤ ∑ x, |g x - c| * |μ x - ν x| :=
      Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [habs, abs_nonneg Δ, h1]
  have hmain : Δ ^ 2 ≤ 2 * d * (distVar μ g + distVar ν g) + d * Δ ^ 2 := by
    have hfin : (∑ x, (g x - c) ^ 2 * |μ x - ν x|) * (2 * d)
        ≤ ((distVar μ g + Δ ^ 2 / 4) + (distVar ν g + Δ ^ 2 / 4)) * (2 * d) := by
      exact mul_le_mul_of_nonneg_right hdom (by linarith)
    nlinarith [hcs, hsq, hfin]
  nlinarith [hmain]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (Φ : V → ℝ) (hΦ : Φ ≠ 0) (lam : ℝ) (heig : P.mulVec Φ = lam • Φ)
    (hlam1 : 1 / 2 < lam) (hlam2 : lam < 1)
    (R : ℝ) (hR : 0 < R)
    (hstep : ∀ x : V, ∑ y, P x y * (Φ y - Φ x) ^ 2 ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (x : V) (hΦx : Φ x ≠ 0) :
    (2 * Real.log (1 / lam))⁻¹ *
        (Real.log ((1 - lam) * Φ x ^ 2 / (2 * R)) + Real.log ((1 - ε) / ε)) ≤
      (mixingTime P π ε : ℝ) := by
  classical
  have hlampos : 0 < lam := by linarith
  have h1lam : 0 < 1 - lam := by linarith
  have h2lam : 0 < 2 * lam - 1 := by linarith
  have hPΦ : ∀ z : V, ∑ y, P z y * Φ y = lam * Φ z := by
    intro z
    have h := congrFun heig z
    simpa [Matrix.mulVec, dotProduct] using h
  set S : ℝ := R / (2 * (1 - lam)) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  have hSfix : (2 * lam - 1) * S + R = S := by
    rw [hSdef]
    field_simp
    ring
  have hstat : ∀ y : V, ∑ z, π z * P z y = π y := fun y => congrFun hπ.2 y
  -- the stationary mean of `Φ` vanishes
  have hEπ : ∑ y, π y * Φ y = 0 := by
    have h1 : ∑ y, π y * Φ y = lam * ∑ z, π z * Φ z := by
      calc ∑ y, π y * Φ y = ∑ y, (∑ z, π z * P z y) * Φ y :=
            Finset.sum_congr rfl fun y _ => by rw [hstat y]
        _ = ∑ z, π z * ∑ y, P z y * Φ y := by
            have e1 : ∀ y : V, (∑ z, π z * P z y) * Φ y = ∑ z, π z * (P z y * Φ y) := by
              intro y
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun z _ => by ring
            rw [Finset.sum_congr rfl fun y _ => e1 y, Finset.sum_comm]
            exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
        _ = ∑ z, π z * (lam * Φ z) := Finset.sum_congr rfl fun z _ => by rw [hPΦ z]
        _ = lam * ∑ z, π z * Φ z := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
    have h2 : (1 - lam) * (∑ y, π y * Φ y) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  -- the stationary second moment
  have hinner : ∀ w : V, ∑ y, P w y * Φ y ^ 2
      = (∑ y, P w y * (Φ y - Φ w) ^ 2) + 2 * Φ w * (lam * Φ w) - Φ w ^ 2 := by
    intro w
    have e : ∀ y : V, P w y * Φ y ^ 2
        = P w y * (Φ y - Φ w) ^ 2 + 2 * Φ w * (P w y * Φ y) - Φ w ^ 2 * P w y := by
      intro y; ring
    rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hPΦ w, ← Finset.mul_sum, hP.2 w, mul_one]
  have hEπ2 : ∑ y, π y * Φ y ^ 2 ≤ S := by
    have hswap : ∑ y, π y * ∑ z, P y z * Φ z ^ 2 = ∑ y, π y * Φ y ^ 2 := by
      have e1 : ∀ y : V, π y * ∑ z, P y z * Φ z ^ 2 = ∑ z, (π y * P y z) * Φ z ^ 2 := by
        intro y
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [Finset.sum_congr rfl fun y _ => e1 y, Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => by rw [← Finset.sum_mul, hstat z]
    have hlhs : ∑ y, π y * (∑ z, P y z * (Φ z - Φ y) ^ 2)
        = 2 * (1 - lam) * ∑ y, π y * Φ y ^ 2 := by
      have e : ∀ y : V, π y * (∑ z, P y z * (Φ z - Φ y) ^ 2)
          = π y * (∑ z, P y z * Φ z ^ 2) - 2 * lam * (π y * Φ y ^ 2)
            + π y * Φ y ^ 2 := by
        intro y
        linear_combination (-(π y)) * hinner y
      rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, hswap, ← Finset.mul_sum]
      ring
    have hrhs : ∑ y, π y * (∑ z, P y z * (Φ z - Φ y) ^ 2) ≤ R := by
      calc ∑ y, π y * (∑ z, P y z * (Φ z - Φ y) ^ 2) ≤ ∑ y, π y * R :=
            Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hstep y) (hπ.1.1 y)
        _ = R := by rw [← Finset.sum_mul, hπ.1.2, one_mul]
    rw [hSdef, le_div_iff₀ (by positivity)]
    linarith [hlhs, hrhs]
  -- powers of `P`
  have hpownn : ∀ (t : ℕ) (z y : V), 0 ≤ (P ^ t) z y := by
    intro t
    induction t with
    | zero => intro z y; by_cases hzy : z = y <;> simp [Matrix.one_apply, hzy]
    | succ n ih =>
        intro z y
        have h : (P ^ (n + 1)) z y = ∑ w, (P ^ n) z w * P w y := by rw [pow_succ]; rfl
        rw [h]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih z w) (hP.1 w y)
  have hrowsum : ∀ (t : ℕ) (z : V), ∑ y, (P ^ t) z y = 1 := by
    intro t
    induction t with
    | zero => intro z; simp [Matrix.one_apply]
    | succ n ih =>
        intro z
        have h : ∀ y : V, (P ^ (n + 1)) z y = ∑ w, (P ^ n) z w * P w y := by
          intro y; rw [pow_succ]; rfl
        rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_comm]
        have h2 : ∀ w : V, ∑ y, (P ^ n) z w * P w y = (P ^ n) z w := by
          intro w; rw [← Finset.mul_sum, hP.2 w, mul_one]
        rw [Finset.sum_congr rfl fun w _ => h2 w, ih z]
  have hpowΦ : ∀ (t : ℕ) (z : V), ∑ y, (P ^ t) z y * Φ y = lam ^ t * Φ z := by
    intro t
    induction t with
    | zero => intro z; simp [Matrix.one_apply]
    | succ n ih =>
        intro z
        have hL : ∀ y : V, (P ^ (n + 1)) z y = ∑ w, (P ^ n) z w * P w y := by
          intro y; rw [pow_succ]; rfl
        have hexp : ∑ y, (P ^ (n + 1)) z y * Φ y
            = ∑ w, (P ^ n) z w * (∑ y, P w y * Φ y) := by
          have e : ∀ y : V, (P ^ (n + 1)) z y * Φ y
              = ∑ w, (P ^ n) z w * (P w y * Φ y) := by
            intro y
            rw [hL y, Finset.sum_mul]
            exact Finset.sum_congr rfl fun w _ => by ring
          rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_comm]
          exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
        rw [hexp, Finset.sum_congr rfl fun w _ => by rw [hPΦ w]]
        have e2 : ∑ w, (P ^ n) z w * (lam * Φ w) = lam * ∑ w, (P ^ n) z w * Φ w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
        rw [e2, ih z, pow_succ]
        ring
  have honestep : ∀ w : V, ∑ y, P w y * Φ y ^ 2 ≤ R + (2 * lam - 1) * Φ w ^ 2 := by
    intro w
    have h2 : 2 * Φ w * (lam * Φ w) - Φ w ^ 2 = (2 * lam - 1) * Φ w ^ 2 := by ring
    linarith [hstep w, hinner w, h2]
  have hpowΦ2 : ∀ (t : ℕ) (z : V),
      ∑ y, (P ^ t) z y * Φ y ^ 2 ≤ (2 * lam - 1) ^ t * Φ z ^ 2 + S := by
    intro t
    induction t with
    | zero =>
        intro z
        have h0 : ∑ y, (P ^ 0) z y * Φ y ^ 2 = Φ z ^ 2 := by simp [Matrix.one_apply]
        rw [h0, pow_zero, one_mul]
        linarith [hSpos]
    | succ n ih =>
        intro z
        have hL : ∀ y : V, (P ^ (n + 1)) z y = ∑ w, (P ^ n) z w * P w y := by
          intro y; rw [pow_succ]; rfl
        have hexp : ∑ y, (P ^ (n + 1)) z y * Φ y ^ 2
            = ∑ w, (P ^ n) z w * (∑ y, P w y * Φ y ^ 2) := by
          have e : ∀ y : V, (P ^ (n + 1)) z y * Φ y ^ 2
              = ∑ w, (P ^ n) z w * (P w y * Φ y ^ 2) := by
            intro y
            rw [hL y, Finset.sum_mul]
            exact Finset.sum_congr rfl fun w _ => by ring
          rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_comm]
          exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
        rw [hexp]
        calc ∑ w, (P ^ n) z w * (∑ y, P w y * Φ y ^ 2)
            ≤ ∑ w, (P ^ n) z w * (R + (2 * lam - 1) * Φ w ^ 2) :=
              Finset.sum_le_sum fun w _ =>
                mul_le_mul_of_nonneg_left (honestep w) (hpownn n z w)
          _ = R + (2 * lam - 1) * ∑ w, (P ^ n) z w * Φ w ^ 2 := by
              have e : ∀ w : V, (P ^ n) z w * (R + (2 * lam - 1) * Φ w ^ 2)
                  = R * (P ^ n) z w + (2 * lam - 1) * ((P ^ n) z w * Φ w ^ 2) := by
                intro w; ring
              rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum, hrowsum n z, mul_one]
          _ ≤ R + (2 * lam - 1) * ((2 * lam - 1) ^ n * Φ z ^ 2 + S) := by
              nlinarith [ih z, h2lam]
          _ = (2 * lam - 1) ^ (n + 1) * Φ z ^ 2 + S := by linear_combination hSfix
  -- variances
  have hvar : ∀ ρ : V → ℝ, IsDist ρ →
      distVar ρ Φ = (∑ y, ρ y * Φ y ^ 2) - (distExp ρ Φ) ^ 2 := by
    intro ρ hρ
    unfold distVar
    have e : ∀ y : V, (Φ y - distExp ρ Φ) ^ 2 * ρ y
        = ρ y * Φ y ^ 2 - 2 * distExp ρ Φ * (Φ y * ρ y) + (distExp ρ Φ) ^ 2 * ρ y := by
      intro y; ring
    have hB : ∑ y, 2 * distExp ρ Φ * (Φ y * ρ y) = 2 * (distExp ρ Φ) ^ 2 := by
      rw [← Finset.mul_sum]
      have he : ∑ y, Φ y * ρ y = distExp ρ Φ := rfl
      rw [he]; ring
    have hC : ∑ y, (distExp ρ Φ) ^ 2 * ρ y = (distExp ρ Φ) ^ 2 := by
      rw [← Finset.mul_sum, hρ.2, mul_one]
    rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hB, hC]
    ring
  -- the key inequality at any time where the chain is `ε`-mixed
  have hkey : ∀ t : ℕ, distStationary P π t ≤ ε →
      lam ^ (2 * t) * ((1 - lam) * Φ x ^ 2 / (2 * R)) ≤ ε / (1 - ε) := by
    intro t hdt
    have hμdist : IsDist (rowDist P t x) := ⟨fun y => hpownn t x y, hrowsum t x⟩
    have hd : tvDist (rowDist P t x) π ≤ ε := by
      refine le_trans ?_ hdt
      exact le_ciSup (Set.Finite.bddAbove
        (Set.range fun z : V => tvDist (rowDist P t z) π).toFinite) x
    have hdnn : 0 ≤ tvDist (rowDist P t x) π := by
      have h := (MarkovMixing.tv_eq_half_l1 (rowDist P t x) π hμdist hπ.1).1
      have h2 : (0 : ℝ) ≤ ∑ y, |rowDist P t x y - π y| :=
        Finset.sum_nonneg fun y _ => abs_nonneg _
      rw [h]; linarith
    have hexpμ : distExp (rowDist P t x) Φ = lam ^ t * Φ x := by
      unfold distExp
      rw [← hpowΦ t x]
      exact Finset.sum_congr rfl fun y _ => by
        show Φ y * (P ^ t) x y = (P ^ t) x y * Φ y
        ring
    have hexpπ : distExp π Φ = 0 := by
      unfold distExp
      rw [← hEπ]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hpow2 : (lam ^ t * Φ x) ^ 2 = lam ^ (2 * t) * Φ x ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm t 2]
    have hvarμ : distVar (rowDist P t x) Φ ≤ S := by
      rw [hvar _ hμdist, hexpμ, hpow2]
      have h1 : ∑ y, rowDist P t x y * Φ y ^ 2 ≤ (2 * lam - 1) ^ t * Φ x ^ 2 + S :=
        hpowΦ2 t x
      have h2 : (2 * lam - 1) ^ t ≤ lam ^ (2 * t) := by
        have hb : 2 * lam - 1 ≤ lam ^ 2 := by nlinarith [sq_nonneg (lam - 1)]
        calc (2 * lam - 1) ^ t ≤ (lam ^ 2) ^ t := pow_le_pow_left₀ (le_of_lt h2lam) hb t
          _ = lam ^ (2 * t) := by rw [← pow_mul]
      nlinarith [h1, h2, sq_nonneg (Φ x)]
    have hvarπ : distVar π Φ ≤ S := by
      rw [hvar π hπ.1, hexpπ]
      have h : ∑ y, π y * Φ y ^ 2 ≤ S := hEπ2
      linarith
    have hvarnn : 0 ≤ distVar (rowDist P t x) Φ + distVar π Φ := by
      have hm : 0 ≤ distVar (rowDist P t x) Φ :=
        Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hμdist.1 y)
      have hp : 0 ≤ distVar π Φ :=
        Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hπ.1.1 y)
      linarith
    have hsm := tv_second_moment (rowDist P t x) π hμdist hπ.1 Φ
    rw [hexpμ, hexpπ, sub_zero] at hsm
    have hstep1 : (lam ^ t * Φ x) ^ 2 * (1 - ε)
        ≤ (lam ^ t * Φ x) ^ 2 * (1 - tvDist (rowDist P t x) π) := by
      nlinarith [sq_nonneg (lam ^ t * Φ x), hd]
    have hstep2 : 2 * tvDist (rowDist P t x) π
        * (distVar (rowDist P t x) Φ + distVar π Φ) ≤ 4 * ε * S := by
      nlinarith [hd, hdnn, hvarμ, hvarπ, hvarnn, hSpos]
    have hA : lam ^ (2 * t) * Φ x ^ 2 * (1 - ε) ≤ 4 * ε * S := by
      rw [← hpow2]
      linarith [hsm, hstep1, hstep2]
    have h4 : 4 * ε * S * (1 - lam) = 2 * ε * R := by
      rw [hSdef]; field_simp; ring
    have hmul := mul_le_mul_of_nonneg_right hA (le_of_lt h1lam)
    have hgoal : lam ^ (2 * t) * ((1 - lam) * Φ x ^ 2 / (2 * R))
        = (lam ^ (2 * t) * ((1 - lam) * Φ x ^ 2)) / (2 * R) := by ring
    rw [hgoal, div_le_iff₀ (show (0 : ℝ) < 2 * R by positivity), div_mul_eq_mul_div,
      le_div_iff₀ (show (0 : ℝ) < 1 - ε by linarith)]
    nlinarith [hmul, h4]
  -- the mixing set is nonempty
  obtain ⟨α, ⟨hα0, hα1⟩, C, hC, hCα⟩ :=
    MarkovMixing.convergence_theorem P hP hirr hap π hπ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / C by positivity) hα1
  have hmemn : distStationary P π n ≤ ε := by
    have h1 : C * α ^ n < C * (ε / C) := mul_lt_mul_of_pos_left hn hC
    have h2 : C * (ε / C) = ε := by field_simp
    rw [h2] at h1
    linarith [hCα n]
  have hd0 : distStationary P π (mixingTime P π ε) ≤ ε :=
    Nat.sInf_mem (⟨n, hmemn⟩ : {t : ℕ | distStationary P π t ≤ ε}.Nonempty)
  have hfinal := hkey (mixingTime P π ε) hd0
  -- take logarithms
  have hΦx2 : 0 < Φ x ^ 2 := by positivity
  have hApos : 0 < (1 - lam) * Φ x ^ 2 / (2 * R) := by positivity
  have hlogstep : Real.log (lam ^ (2 * mixingTime P π ε) * ((1 - lam) * Φ x ^ 2 / (2 * R)))
      ≤ Real.log (ε / (1 - ε)) := Real.log_le_log (by positivity) hfinal
  rw [Real.log_mul (by positivity) (ne_of_gt hApos), Real.log_pow] at hlogstep
  have hlogB : Real.log ((1 - ε) / ε) = -Real.log (ε / (1 - ε)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hloglam : Real.log (1 / lam) = -Real.log lam := by rw [one_div, Real.log_inv]
  have hloglampos : 0 < Real.log (1 / lam) := by
    rw [hloglam]
    have h := Real.log_neg hlampos hlam2
    linarith
  rw [inv_mul_eq_div, div_le_iff₀ (by linarith), hlogB, hloglam]
  push_cast at hlogstep ⊢
  linarith [hlogstep]
