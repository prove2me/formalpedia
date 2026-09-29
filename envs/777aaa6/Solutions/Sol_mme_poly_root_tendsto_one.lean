-- Prove2me | solution 1 for mme_poly_root_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:44:13.475265+00:00
-- url     : https://prove2.me/submissions/8a47628e-3cbb-4ae0-afe5-4c4b1f4af5ac

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Topology

theorem solution (a b : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((((n + 1) * a + 1) ^ b : ℕ) : ℝ) ^ ((1 : ℝ) / (n + 1)))
      Filter.atTop (nhds 1) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  -- (n+1)^(b/(n+1)) → 1
  have hg1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1))) atTop (nhds 1) := by
    have h := (tendsto_rpow_div_mul_add (b : ℝ) 1 0 (by norm_num)).comp hbase
    simpa using h
  -- b/(n+1) → 0
  have hexp0 : Tendsto (fun n : ℕ => (b : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hbase
  -- (a+1)^(b/(n+1)) → 1
  have hg2 : Tendsto (fun n : ℕ => ((a : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1))) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => ((a : ℝ) + 1)) atTop (nhds ((a : ℝ) + 1)) :=
      tendsto_const_nhds
    have h := Filter.Tendsto.rpow hconst hexp0 (Or.inl (by positivity))
    simpa [Real.rpow_zero] using h
  have hg : Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1))
          * ((a : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1))) atTop (nhds 1) := by
    simpa using hg1.mul hg2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
  · -- 1 ≤ f n
    intro n
    dsimp only
    have h1x : (1 : ℝ) ≤ ((((n + 1) * a + 1) ^ b : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow b ((n + 1) * a + 1) (by omega)
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) := (Real.one_rpow _).symm
      _ ≤ ((((n + 1) * a + 1) ^ b : ℕ) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) :=
          Real.rpow_le_rpow (by norm_num) h1x (by positivity)
  · -- f n ≤ g n
    intro n
    dsimp only
    have hy0 : (0 : ℝ) ≤ (((n + 1) * a + 1 : ℕ) : ℝ) := by positivity
    have hf : ((((n + 1) * a + 1) ^ b : ℕ) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))
            = (((n + 1) * a + 1 : ℕ) : ℝ) ^ ((b : ℝ) / ((n : ℝ) + 1)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (((n + 1) * a + 1 : ℕ) : ℝ) b,
          ← Real.rpow_mul hy0, mul_one_div]
    rw [hf]
    have hle : (((n + 1) * a + 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) * ((a : ℝ) + 1) := by
      push_cast
      nlinarith [(by positivity : (0 : ℝ) ≤ (n : ℝ)), (by positivity : (0 : ℝ) ≤ (a : ℝ))]
    calc (((n + 1) * a + 1 : ℕ) : ℝ) ^ ((b : ℝ) / ((n : ℝ) + 1))
        ≤ (((n : ℝ) + 1) * ((a : ℝ) + 1)) ^ ((b : ℝ) / ((n : ℝ) + 1)) :=
          Real.rpow_le_rpow hy0 hle (by positivity)
      _ = ((n : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1)) * ((a : ℝ) + 1) ^ ((b : ℝ) / ((n : ℝ) + 1)) :=
          Real.mul_rpow (by positivity) (by positivity)
