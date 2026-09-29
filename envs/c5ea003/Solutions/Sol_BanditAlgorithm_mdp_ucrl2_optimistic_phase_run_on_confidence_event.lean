-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_confidence_event
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T21:13:48.06499+00:00
-- url     : https://prove2.me/submissions/b230db60-e5b3-4ef0-aacb-abf56c8eb4b4

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_with_confidence_widths
import Theorems.Thm_BanditAlgorithm_mdp_inner_prob_diff_le_half_l1_mul_span
import Theorems.Thm_BanditAlgorithm_mdp_doubling_phase_visit_sum_aggregate_le

open MeasureTheory ProbabilityTheory ENNReal BanditAlgorithm

/-!
The accumulated estimation error of an optimistic phase run.

The run of the algorithm carries more information than the certificate needs:
in each phase the optimistic transition row of the played pair lies in the same
`L¹` ball as the true one, so the two are within twice the confidence radius of
each other, and the visit counts satisfy the doubling inequality that ends a
phase.  This file turns that local information into the single aggregate bound
that the regret analysis consumes: Hölder against the span of the bias converts
each round into the confidence radius of the pair played, and the doubling
inequality sums those radii to `(√2 + 1)√(SAn)`.
-/

theorem solution
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : MDPPolicy S A,
      ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating → 1 ≤ mdpDiameter M →
        ∀ μ0 : MDPStateDistribution S,
          ∃ E : Set (MDPTrajectory S A n),
            mdpMeasure M μ0 π n Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
            ∀ h ∈ mdpConfidenceGoodEvent M n δ ∩ E,
            ∃ (st : ℕ → Fin S) (act : ℕ → Fin A) (K : ℕ) (τ : ℕ → ℕ)
              (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ) (q : ℕ → Fin S → Fin S → ℝ),
              (∀ t : Fin n, h t = (st t, act t)) ∧
              τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
              (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
              (∀ k < K, mdpOptimalGain M ≤ ρ k) ∧
              (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ρ k + v k (st t)
                  = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
                ≤ mdpDiameter M * (Real.sqrt 2 + 1) *
                    Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
                    Real.sqrt (S * A * n)) ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) := by
  classical
  obtain ⟨π, hrun⟩ :=
    BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_with_confidence_widths
      S A n hS hA hn δ hδ r hr
  refine ⟨π, ?_⟩
  intro M hMr hMcomm hMD μ0
  obtain ⟨E, hE, hcert⟩ := hrun M hMr hMcomm hMD μ0
  refine ⟨E, hE, ?_⟩
  intro h hh
  obtain ⟨st, act, K, τ, ρ, v, q, N, ν, hsa, hτ0, hτK, hτm, hK, hopt, hspan,
    hqsum, hbell, hN0, hνnn, hNstep, hdouble, hNtot, hcount, hwidth, hmart⟩ :=
    hcert h hh
  refine ⟨st, act, K, τ, ρ, v, q, hsa, hτ0, hτK, hτm, hK, hopt, hspan, hbell,
    ?_, hmart⟩
  -- notation
  have hD0 : (0 : ℝ) ≤ mdpDiameter M := by linarith
  have hS0 : 0 < S := by omega
  have hLnn : (0 : ℝ) ≤ 14 * S * Real.log (2 * S * A * n / δ) := by
    obtain ⟨hδ0, hδ1⟩ := hδ
    have hSR : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have e1 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A :=
      mul_le_mul (by linarith) hAR (by norm_num) (by linarith)
    have e2 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A * n :=
      mul_le_mul (by linarith) hnR (by norm_num) (by linarith)
    have hY1 : (1 : ℝ) ≤ 2 * S * A * n / δ := by
      rw [le_div_iff₀ hδ0]; nlinarith
    exact mul_nonneg (by positivity) (Real.log_nonneg hY1)
  -- the width of the confidence ball of the pair played at round `t` of phase `k`
  set W : ℕ → Fin S → Fin A → ℝ := fun k s a ↦
    Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) / Real.sqrt (max 1 (N k s a))
    with hWdef
  set U : ℕ → Fin S → Fin A → ℝ := fun k s a ↦
    ν k s a / Real.sqrt (max 1 (N k s a)) with hUdef
  have hWeq : ∀ k s a,
      Real.sqrt (14 * S * Real.log (2 * S * A * n / δ) / max 1 (N k s a)) = W k s a := by
    intro k s a
    rw [hWdef]
    exact Real.sqrt_div hLnn _
  -- Step 1: Hölder against the span turns each round into the confidence width
  have hround : ∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
      ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
        ≤ mdpDiameter M * W k (st t) (act t) := by
    intro k hk t ht
    obtain ⟨s0, -, hs0⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin S)) (v k)
        ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
    have hv : ∀ s', v k s' ∈ Set.Icc (v k s0) (v k s0 + mdpDiameter M) := by
      intro s'
      exact ⟨hs0 s' (Finset.mem_univ _), by linarith [hspan k hk s' s0]⟩
    have hPsum : ∑ s', ((M.P (st t) (act t) s' : ℝ)) = 1 := by
      rw [← NNReal.coe_sum, M.P_sum_one]; simp
    have hholder :=
      BanditAlgorithm.mdp_inner_prob_diff_le_half_l1_mul_span
        (q k (st t)) (fun s' ↦ ((M.P (st t) (act t) s' : ℝ))) (v k)
        (v k s0) (v k s0 + mdpDiameter M) (hqsum k hk (st t)) hPsum hv
    have hspanval : v k s0 + mdpDiameter M - v k s0 = mdpDiameter M := by ring
    rw [hspanval] at hholder
    refine hholder.trans ?_
    have hw := hwidth k hk t ht
    rw [hWeq] at hw
    calc (∑ s', |q k (st t) s' - ((M.P (st t) (act t) s' : ℝ))|) / 2 * mdpDiameter M
        ≤ (2 * W k (st t) (act t)) / 2 * mdpDiameter M :=
          mul_le_mul_of_nonneg_right (by linarith) hD0
      _ = mdpDiameter M * W k (st t) (act t) := by ring
  -- Step 2: sum over a phase, converting rounds into visit counts
  have hphase : ∀ k < K,
      ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
          ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
        ≤ mdpDiameter M * ∑ s, ∑ a, ν k s a * W k s a := by
    intro k hk
    calc ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
            ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
        ≤ ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), mdpDiameter M * W k (st t) (act t) :=
          Finset.sum_le_sum fun t ht ↦ hround k hk t ht
      _ = mdpDiameter M * ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), W k (st t) (act t) := by
          rw [Finset.mul_sum]
      _ = mdpDiameter M * ∑ s, ∑ a, ν k s a * W k s a := by
          rw [hcount k hk (W k)]
  -- Step 3: the doubling inequality sums the widths across phases
  have hagg :=
    BanditAlgorithm.mdp_doubling_phase_visit_sum_aggregate_le
      (ι := Fin S × Fin A) (fun i k ↦ N k i.1 i.2) (fun i k ↦ ν k i.1 i.2)
      (n : ℝ) K (fun i ↦ hN0 i.1 i.2) (fun i k ↦ hνnn k i.1 i.2)
      (fun i k ↦ hNstep k i.1 i.2) (fun i k ↦ hdouble k i.1 i.2)
      (by rw [Fintype.sum_prod_type]; exact hNtot)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul] at hagg
  -- Step 4: assemble
  have hconst : ∀ k : ℕ,
      mdpDiameter M * ∑ s, ∑ a, ν k s a * W k s a
        = mdpDiameter M * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
            ∑ s, ∑ a, U k s a := by
    intro k
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [hWdef, hUdef]
    ring
  have hswap : ∑ k ∈ Finset.range K, ∑ s : Fin S, ∑ a : Fin A, U k s a
      = ∑ i : Fin S × Fin A, ∑ k ∈ Finset.range K, U k i.1 i.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.sum_comm]
  calc ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
          ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
      ≤ ∑ k ∈ Finset.range K, mdpDiameter M * ∑ s, ∑ a, ν k s a * W k s a :=
        Finset.sum_le_sum fun k hk ↦ hphase k (Finset.mem_range.1 hk)
    _ = ∑ k ∈ Finset.range K, (mdpDiameter M *
          Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) * ∑ s, ∑ a, U k s a) :=
        Finset.sum_congr rfl fun k _ ↦ hconst k
    _ = mdpDiameter M * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
          ∑ k ∈ Finset.range K, ∑ s, ∑ a, U k s a := by rw [Finset.mul_sum]
    _ = mdpDiameter M * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
          ∑ i : Fin S × Fin A, ∑ k ∈ Finset.range K, U k i.1 i.2 := by rw [hswap]
    _ ≤ mdpDiameter M * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
          ((Real.sqrt 2 + 1) * Real.sqrt ((S : ℝ) * A * n)) := by
        refine mul_le_mul_of_nonneg_left hagg ?_
        exact mul_nonneg hD0 (Real.sqrt_nonneg _)
    _ = mdpDiameter M * (Real.sqrt 2 + 1) *
          Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
          Real.sqrt (S * A * n) := by ring
