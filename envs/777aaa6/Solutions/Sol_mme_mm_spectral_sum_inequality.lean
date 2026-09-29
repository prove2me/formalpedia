-- Prove2me | solution 1 for mme_mm_spectral_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:33.384732+00:00
-- url     : https://prove2.me/submissions/281d49e5-690f-48c6-b63c-31602922686f

import Definitions.Def_mme_tensor_bridge

/-! # Solution: abstract sum inequality instantiated at `mmTensorData K`.

`MMData.sum_inequality` (`Def_mme_mm_spectral`) is the abstract asymptotic-spectrum sum
inequality applied to a general `MMData` bundle. Instantiated at `mmTensorData K`
(declared in `Def_mme_tensor_bridge`), it yields exactly this leaf. -/

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] {k : ℕ}
    (n m p : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i)
    (r : ℕ)
    (h : StrassenPreorder.asymptoticRank (tensorPreorder K)
        (∑ i, MMq K (n i) (m i) (p i)) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ ((mmTensorData K).omegaAbs / 3) ≤ r :=
  (mmTensorData K).sum_inequality n m p hn hm hp r h
