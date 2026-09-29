-- Prove2me | solution 1 for BanditAlgorithm.mdp_optimal_gain_ge_of_reverse_bellman_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T15:13:27.805525+00:00
-- url     : https://prove2.me/submissions/ce8a19ce-3ee7-4132-93dc-285b06e91b83

import Theorems.Thm_BanditAlgorithm_mdp_expected_reward_ge_of_reverse_bellman_ineq

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
The gain of the memoryless deterministic policy `f` is the Cesaro limsup of
`E[reward]/n`, which the finite-horizon bound `n ρ - span(v)` pins from below;
since the optimal gain is a supremum over states and policies (bounded above by
one, the rewards being in `[0,1]`), it dominates `ρ`.
-/

variable {S A : ℕ}
/-- The average reward per round is at most one. -/
private lemma expected_reward_div_le_one (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) : mdpExpectedReward M μ0 π n / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrew : mdpExpectedReward M μ0 π n ≤ n := by
    rw [mdpExpectedReward]
    calc ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M μ0 π n)
        ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M μ0 π n) := by
          refine integral_mono Integrable.of_finite Integrable.of_finite fun h ↦ ?_
          calc mdpTrajectoryReward M h ≤ ∑ _t : Fin n, (1 : ℝ) :=
                Finset.sum_le_sum fun t _ ↦ (M.r_mem_Icc (h t).1 (h t).2).2
            _ = (n : ℝ) := by simp
      _ = (n : ℝ) := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  rw [div_le_one hnR]
  exact hrew

/-- The gain of any policy is at most one, because the rewards are. -/
private lemma gain_le_one (M : FiniteMDP S A) (π : MDPPolicy S A) (s : Fin S) :
    mdpGain M π s ≤ 1 := by
  set u : ℕ → ℝ := fun n ↦ mdpExpectedReward M (mdpStateDirac s) π n / n with hu
  have hlow : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    have hrew : (0 : ℝ) ≤ mdpExpectedReward M (mdpStateDirac s) π n := by
      rw [mdpExpectedReward]
      refine integral_nonneg fun h ↦ ?_
      exact Finset.sum_nonneg fun t _ ↦ (M.r_mem_Icc (h t).1 (h t).2).1
    exact div_nonneg hrew (Nat.cast_nonneg n)
  have hupp : ∀ n : ℕ, u n ≤ 1 := fun n ↦ expected_reward_div_le_one M _ π n
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isCoboundedUnder_le_of_le _ hlow
  exact Filter.limsup_le_of_le hcob (Filter.Eventually.of_forall hupp)

/-- **The gain of the greedy policy is at least `ρ`.** -/
private theorem gain_ge_of_reverse_bellman_ineq (M : FiniteMDP S A) (f : Fin S → Fin A)
    (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') (s : Fin S) :
    ρ ≤ mdpGain M (mdpMemorylessDetPolicy f) s := by
  have hlohi : lo ≤ hi := le_trans (hv s).1 (hv s).2
  set u : ℕ → ℝ :=
    fun n ↦ mdpExpectedReward M (mdpStateDirac s) (mdpMemorylessDetPolicy f) n / n with hu
  set w : ℕ → ℝ := fun n ↦ ρ - (hi - lo) / n with hw
  have hle : ∀ᶠ n : ℕ in Filter.atTop, w n ≤ u n := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hbnd :=
      BanditAlgorithm.mdp_expected_reward_ge_of_reverse_bellman_ineq M (mdpStateDirac s) f ρ v lo hi hv hbell n
    rw [hu, hw, le_div_iff₀ hnR]
    field_simp
    linarith
  have hwlim : Filter.Tendsto w Filter.atTop (nhds ρ) := by
    have : Filter.Tendsto (fun n : ℕ ↦ (hi - lo) / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa [hw] using tendsto_const_nhds.sub this
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop w := by
    refine Filter.isCoboundedUnder_le_of_le _ (x := ρ - (hi - lo)) fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hw, hn]; linarith
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (hi - lo) / n ≤ hi - lo := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    simp only [hw]
    linarith
  have hbd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of
      ⟨1, fun n ↦ expected_reward_div_le_one M (mdpStateDirac s)
        (mdpMemorylessDetPolicy f) n⟩
  calc ρ = Filter.limsup w Filter.atTop := hwlim.limsup_eq.symm
    _ ≤ Filter.limsup u Filter.atTop := Filter.limsup_le_limsup hle hcob hbd
    _ = mdpGain M (mdpMemorylessDetPolicy f) s := rfl

theorem solution {S A : ℕ} (hS : 0 < S) (M : FiniteMDP S A)
    (f : Fin S → Fin A) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') :
    ρ ≤ mdpOptimalGain M := by
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  set s₀ : Fin S := Classical.arbitrary (Fin S) with hs₀
  have hbddπ : ∀ s : Fin S, BddAbove (Set.range fun π : MDPPolicy S A ↦ mdpGain M π s) := by
    intro s
    exact ⟨1, by rintro _ ⟨π, rfl⟩; exact gain_le_one M π s⟩
  have hbdds : BddAbove (Set.range fun s : Fin S ↦ ⨆ π : MDPPolicy S A, mdpGain M π s) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    haveI : Nonempty (MDPPolicy S A) := ⟨mdpMemorylessDetPolicy f⟩
    exact ciSup_le fun π ↦ gain_le_one M π s
  calc ρ ≤ mdpGain M (mdpMemorylessDetPolicy f) s₀ :=
        gain_ge_of_reverse_bellman_ineq M f ρ v lo hi hv hbell s₀
    _ ≤ ⨆ π : MDPPolicy S A, mdpGain M π s₀ := le_ciSup (hbddπ s₀) _
    _ ≤ mdpOptimalGain M := le_ciSup hbdds s₀
