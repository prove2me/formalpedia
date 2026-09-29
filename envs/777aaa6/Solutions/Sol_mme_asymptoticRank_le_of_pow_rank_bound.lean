-- Prove2me | solution 1 for mme_asymptoticRank_le_of_pow_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:44:12.131241+00:00
-- url     : https://prove2.me/submissions/864a6c76-901c-4725-93d0-fcccf924541d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_tensor_rank

open MME Filter Topology

universe u

theorem solution {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) (r : ℕ) (C : ℕ → ℝ)
    (hC1 : ∀ n, (1 : ℝ) ≤ C n)
    (hlim : Filter.Tendsto (fun n => (C (n + 1)) ^ ((1 : ℝ) / (n + 1))) Filter.atTop (nhds 1))
    (hbound : ∀ n, (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ)
                    ≤ (r : ℝ) ^ (n + 1) * C (n + 1)) :
    tensorAsymptoticRank X ≤ r := by
  rw [tensorAsymptoticRank]
  set a : ℕ → ℝ :=
    fun n => (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1)) with ha
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩; rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (by positivity) _
  -- each term is bounded by `r * C(n+1)^(1/(n+1))`
  have hstep : ∀ n, a n ≤ (r : ℝ) * (C (n + 1)) ^ ((1 : ℝ) / (n + 1)) := by
    intro n
    have hCpos : (0 : ℝ) ≤ C (n + 1) := le_trans zero_le_one (hC1 _)
    have hrank0 : (0 : ℝ) ≤ (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) := by positivity
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    calc a n = (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1)) := rfl
      _ ≤ ((r : ℝ) ^ (n + 1) * C (n + 1)) ^ ((1 : ℝ) / (n + 1)) :=
          Real.rpow_le_rpow hrank0 (hbound n) (by positivity)
      _ = ((r : ℝ) ^ (n + 1)) ^ ((1 : ℝ) / (n + 1)) * (C (n + 1)) ^ ((1 : ℝ) / (n + 1)) := by
          rw [Real.mul_rpow (by positivity) hCpos]
      _ = (r : ℝ) * (C (n + 1)) ^ ((1 : ℝ) / (n + 1)) := by
          congr 1
          rw [← Real.rpow_natCast (r : ℝ) (n + 1), ← Real.rpow_mul hr0]
          push_cast
          rw [mul_one_div, div_self hne, Real.rpow_one]
  -- the bounding sequence tends to `r`
  have hlim_r : Tendsto (fun n => (r : ℝ) * (C (n + 1)) ^ ((1 : ℝ) / (n + 1))) atTop (nhds (r : ℝ)) := by
    have := hlim.const_mul (r : ℝ)
    simpa using this
  -- ⨅ a ≤ r
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨N, hN⟩ :=
    (hlim_r.eventually (eventually_lt_nhds (show (r : ℝ) < r + ε by linarith))).exists
  calc ⨅ n, a n ≤ a N := ciInf_le hbdd N
    _ ≤ (r : ℝ) * (C (N + 1)) ^ ((1 : ℝ) / (N + 1)) := hstep N
    _ ≤ r + ε := le_of_lt hN
