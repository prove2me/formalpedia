-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_regret_bound_of_optimistic_phase_run
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T20:07:48.496066+00:00
-- url     : https://prove2.me/submissions/9663db57-96df-471d-9337-00a099689c58

import Definitions.Def_FiniteMDPLearning
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-!
The deterministic half of the analysis of UCRL2: an optimistic phase run of a
trajectory forces the regret bound of Theorem 38.6.
-/

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 2 ≤ S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ M : FiniteMDP S A, 1 ≤ mdpDiameter M →
            ∀ (h : MDPTrajectory S A n) (st : ℕ → Fin S) (act : ℕ → Fin A),
              (∀ t : Fin n, h t = (st t, act t)) →
              ∀ (K : ℕ) (τ : ℕ → ℕ) (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ)
                (q : ℕ → Fin S → Fin S → ℝ),
                τ 0 = 0 → τ K = n → (∀ k, τ k ≤ τ (k + 1)) →
                (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) →
                (∀ k < K, mdpOptimalGain M ≤ ρ k) →
                (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) →
                (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ρ k + v k (st t)
                    = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') →
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
                  ≤ mdpDiameter M * (Real.sqrt 2 + 1) *
                      Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
                      Real.sqrt (S * A * n)) →
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                  ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) →
                mdpRegret M n h <
                  C * mdpDiameter M * S *
                    Real.sqrt (A * n * Real.log (n * S * A / δ)) := by
  -- A uniform tool for the square-root estimates at the end.
  have key : ∀ x y c : ℝ, 0 ≤ c → x ≤ c ^ 2 * y → Real.sqrt x ≤ c * Real.sqrt y := by
    intro x y c hc hxy
    have h1 : Real.sqrt x ≤ Real.sqrt (c ^ 2 * y) := Real.sqrt_le_sqrt hxy
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hc] at h1
  -- Telescoping over an interval.
  have htel : ∀ (f : ℕ → ℝ) (a b : ℕ), a ≤ b →
      ∑ t ∈ Finset.Ico a b, (f (t + 1) - f t) = f b - f a := by
    intro f a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring
  refine ⟨24, by norm_num, ?_⟩
  intro S A n hS hA hn δ hδ M hMD h st act hsa K τ ρ v q hτ0 hτK hτm hK hopt
    hspan hbell hest hmart
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hτmono : ∀ i j : ℕ, i ≤ j → τ i ≤ τ j := fun i j hij =>
    monotone_nat_of_le_succ hτm hij
  -- Numeric preliminaries.
  have hDpos : (0 : ℝ) < mdpDiameter M := lt_of_lt_of_le zero_lt_one hMD
  have hSR : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((n : ℝ) * S * A / δ) := ⟨_, rfl⟩
  have hnS : (2 : ℝ) ≤ (n : ℝ) * S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (sub_nonneg.mpr hSR)]
  have hprod : (2 : ℝ) ≤ (n : ℝ) * S * A := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) * S) (sub_nonneg.mpr hAR)]
  have hnum : (0 : ℝ) < (n : ℝ) * S * A := by linarith
  have hAnpos : (0 : ℝ) < (A : ℝ) * n := mul_pos (by linarith) (by linarith)
  have harg : (2 : ℝ) ≤ (n : ℝ) * S * A / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hx := Real.add_one_le_exp (-Real.log 2)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hx
    norm_num at hx
    linarith
  have hL : Real.log 2 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) harg
  have hLpos : (0 : ℝ) < L := by linarith
  -- The confidence-radius logarithm is at most twice `L`.
  have hL' : Real.log (2 * (S : ℝ) * A * n / δ) ≤ 2 * L := by
    have heq : 2 * (S : ℝ) * A * n / δ = 2 * ((n : ℝ) * S * A / δ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [heq, Real.log_mul (by norm_num) (ne_of_gt (div_pos hnum hδ0)), ← hLdef]
    linarith
  -- The martingale logarithm is at most `L`.
  have hL2δ : Real.log (2 / δ) ≤ L := by
    have h2δ : (2 : ℝ) / δ ≤ (n : ℝ) * S * A / δ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hprod (inv_pos.mpr hδ0).le
    rw [hLdef]
    exact Real.log_le_log (div_pos (by norm_num) hδ0) h2δ
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.sqrt ((A : ℝ) * n * L) := ⟨_, rfl⟩
  have hTpos : (0 : ℝ) < T := by
    rw [hTdef]; exact Real.sqrt_pos.mpr (mul_pos hAnpos hLpos)
  rw [← hLdef, ← hTdef]
  -- ### Step 1: the regret as a sum over the phases.
  have hpart : ∀ (g : ℕ → ℝ) (m : ℕ),
      ∑ k ∈ Finset.range m, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), g t
        = ∑ t ∈ Finset.Ico (τ 0) (τ m), g t := by
    intro g m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive g (hτmono 0 m (Nat.zero_le m)) (hτm m)
  have hrew : ∑ t : Fin n, M.r (h t).1 (h t).2
      = ∑ t ∈ Finset.range n, M.r (st t) (act t) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => M.r (st i) (act i)) n]
    exact Finset.sum_congr rfl fun t _ => by simp [hsa t]
  have hreg : mdpRegret M n h
      = ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
          (mdpOptimalGain M - M.r (st t) (act t)) := by
    rw [hpart, hτ0, hτK, ← Finset.range_eq_Ico, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, mdpRegret, mdpTrajectoryReward, hrew]
    simp [mul_comm]
  -- ### Step 2: the per-phase telescoping.
  have hkey : ∀ k, k < K →
      ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), (mdpOptimalGain M - M.r (st t) (act t))
        ≤ (v k (st (τ (k + 1))) - v k (st (τ k)))
          + (∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
              ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
          + ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
              ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s' := by
    intro k hk
    have hstep : ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
        mdpOptimalGain M - M.r (st t) (act t)
          ≤ ((v k (st (t + 1)) - v k (st t))
              + ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
            + ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s' := by
      intro t ht
      have hb := hbell k hk t ht
      have ho := hopt k hk
      have hsplit : ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
          = (∑ s', q k (st t) s' * v k s')
            - ∑ s', (M.P (st t) (act t) s' : ℝ) * v k s' := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by ring
      rw [hsplit]; linarith
    calc ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
            (mdpOptimalGain M - M.r (st t) (act t))
        ≤ ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
            (((v k (st (t + 1)) - v k (st t))
                + ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
              + ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s') :=
          Finset.sum_le_sum hstep
      _ = (v k (st (τ (k + 1))) - v k (st (τ k)))
            + (∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
            + ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s' := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            htel (fun t => v k (st t)) _ _ (hτm k)]
  -- ### Step 3: collect the three groups of terms.
  have hboundary : ∑ k ∈ Finset.range K, (v k (st (τ (k + 1))) - v k (st (τ k)))
      ≤ (K : ℝ) * mdpDiameter M := by
    calc ∑ k ∈ Finset.range K, (v k (st (τ (k + 1))) - v k (st (τ k)))
        ≤ ∑ _k ∈ Finset.range K, mdpDiameter M :=
          Finset.sum_le_sum fun k hk =>
            hspan k (Finset.mem_range.mp hk) _ _
      _ = (K : ℝ) * mdpDiameter M := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcollect : mdpRegret M n h
      ≤ (K : ℝ) * mdpDiameter M
        + mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))
        + mdpDiameter M * (Real.sqrt 2 + 1) *
            Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
            Real.sqrt (S * A * n) := by
    rw [hreg]
    calc ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
            (mdpOptimalGain M - M.r (st t) (act t))
        ≤ ∑ k ∈ Finset.range K,
            ((v k (st (τ (k + 1))) - v k (st (τ k)))
              + (∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
              + ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s') :=
          Finset.sum_le_sum fun k hk => hkey k (Finset.mem_range.mp hk)
      _ = (∑ k ∈ Finset.range K, (v k (st (τ (k + 1))) - v k (st (τ k))))
            + (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1))))
            + ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s' := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ _ := by
          exact add_le_add (add_le_add hboundary hmart) hest
  -- ### Step 4: the arithmetic.
  have hsqrt2 : Real.sqrt 2 ≤ 1.5 := by
    have := key 2 1 1.5 (by norm_num) (by norm_num)
    simpa using this
  -- the phase-count term
  have hSnn : (0 : ℝ) ≤ (S : ℝ) := by linarith
  have hXnn : (0 : ℝ) ≤ (A : ℝ) * n := hAnpos.le
  have hA1 : Real.sqrt ((S : ℝ) * A * n) ≤ (4 / 3 * S) * T := by
    rw [hTdef]
    refine key _ _ _ (by positivity) ?_
    have h1 : (1 : ℝ) ≤ 16 / 9 * S * L := by
      linarith [mul_nonneg (sub_nonneg.mpr hSR) (by linarith : (0 : ℝ) ≤ L - 1 / 2)]
    linarith [mul_nonneg (mul_nonneg hSnn hXnn) (sub_nonneg.mpr h1)]
  -- the martingale term
  have hA2 : Real.sqrt (2 * (n : ℝ) * Real.log (2 / δ)) ≤ 2 * T := by
    rw [hTdef]
    refine key _ _ _ (by norm_num) ?_
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ)) (sub_nonneg.mpr hL2δ),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ)) hLpos.le)
        (sub_nonneg.mpr hAR),
      mul_nonneg hXnn hLpos.le]
  -- the estimation term
  have hA3 : Real.sqrt (14 * (S : ℝ) * Real.log (2 * S * A * n / δ))
      * Real.sqrt ((S : ℝ) * A * n) ≤ (6 * S) * T := by
    have hlog0 : (0 : ℝ) ≤ Real.log (2 * (S : ℝ) * A * n / δ) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ0]; nlinarith
    have hx0 : (0 : ℝ) ≤ 14 * (S : ℝ) * Real.log (2 * (S : ℝ) * A * n / δ) :=
      mul_nonneg (by positivity) hlog0
    rw [hTdef, ← Real.sqrt_mul hx0]
    refine key _ _ _ (by positivity) ?_
    have hSAn : (0 : ℝ) ≤ (S : ℝ) ^ 2 * ((A : ℝ) * n) := by positivity
    linarith [mul_nonneg hSAn (sub_nonneg.mpr hL'), mul_nonneg hSAn hLpos.le]
  -- put the three together
  have hfinal : (K : ℝ) * mdpDiameter M
      + mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))
      + mdpDiameter M * (Real.sqrt 2 + 1) *
          Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
          Real.sqrt (S * A * n)
      ≤ 21 * mdpDiameter M * S * T := by
    have e1 : (K : ℝ) * mdpDiameter M ≤ 4 * mdpDiameter M * S * T := by
      have hKle : (K : ℝ) ≤ 4 * S * T := by
        calc (K : ℝ) ≤ 3 * Real.sqrt ((S : ℝ) * A * n) := hK
          _ ≤ 3 * ((4 / 3 * S) * T) := by linarith
          _ = 4 * S * T := by ring
      linarith [mul_nonneg hDpos.le (sub_nonneg.mpr hKle)]
    have e2 : mdpDiameter M * Real.sqrt (2 * (n : ℝ) * Real.log (2 / δ))
        ≤ 2 * mdpDiameter M * S * T := by
      linarith [mul_le_mul_of_nonneg_left hA2 hDpos.le,
        mul_nonneg (mul_nonneg hDpos.le hTpos.le) (by linarith : (0 : ℝ) ≤ (S : ℝ) - 1)]
    have e3 : mdpDiameter M * (Real.sqrt 2 + 1) *
        Real.sqrt (14 * (S : ℝ) * Real.log (2 * S * A * n / δ)) *
        Real.sqrt ((S : ℝ) * A * n) ≤ 15 * mdpDiameter M * S * T := by
      have hp : (0 : ℝ) ≤ mdpDiameter M * (Real.sqrt 2 + 1) :=
        mul_nonneg hDpos.le (by positivity)
      have h1 : mdpDiameter M * (Real.sqrt 2 + 1) *
          (Real.sqrt (14 * (S : ℝ) * Real.log (2 * S * A * n / δ)) *
            Real.sqrt ((S : ℝ) * A * n))
          ≤ mdpDiameter M * (Real.sqrt 2 + 1) * ((6 * S) * T) :=
        mul_le_mul_of_nonneg_left hA3 hp
      have h2 : mdpDiameter M * (Real.sqrt 2 + 1) * ((6 * S) * T)
          ≤ 15 * mdpDiameter M * S * T := by
        linarith [mul_nonneg (mul_nonneg (mul_nonneg hDpos.le hSnn) hTpos.le)
          (sub_nonneg.mpr hsqrt2)]
      calc mdpDiameter M * (Real.sqrt 2 + 1) *
            Real.sqrt (14 * (S : ℝ) * Real.log (2 * S * A * n / δ)) *
            Real.sqrt ((S : ℝ) * A * n)
          = mdpDiameter M * (Real.sqrt 2 + 1) *
              (Real.sqrt (14 * (S : ℝ) * Real.log (2 * S * A * n / δ)) *
                Real.sqrt ((S : ℝ) * A * n)) := by ring
        _ ≤ _ := h1
        _ ≤ _ := h2
    linarith
  have hstrict : 21 * mdpDiameter M * S * T < 24 * mdpDiameter M * S * T := by
    linarith [mul_pos (mul_pos hDpos (by linarith : (0 : ℝ) < (S : ℝ))) hTpos]
  calc mdpRegret M n h ≤ _ := hcollect
    _ ≤ 21 * mdpDiameter M * S * T := hfinal
    _ < 24 * mdpDiameter M * S * T := hstrict
