-- Prove2me | solution 1 for mme_asymptotic_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:37.3489+00:00
-- url     : https://prove2.me/submissions/c12fca5f-14c1-4c59-a5ca-6e7890206b31

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_omega_strassen
import Theorems.Thm_mme_sum_inequality

/-! # Sketch: Schönhage's asymptotic sum inequality (the `τ` theorem)

`mme_asymptotic_sum_inequality` is exactly the general (zero-dimension-tolerant) concrete
sum inequality `mme_sum_inequality`. The sketch is a one-line citation of that child. -/

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] {k : ℕ}
    (n m p : Fin k → ℕ) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r :=
  MME.mme_sum_inequality n m p r h
