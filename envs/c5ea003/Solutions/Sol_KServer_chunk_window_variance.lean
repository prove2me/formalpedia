-- Prove2me | solution 1 for KServer.chunk_window_variance
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T13:37:57.759576+00:00
-- url     : https://prove2.me/submissions/fc2dfb44-e779-4fcc-b480-b1ea1f29e813

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) :
    ∑ ω, C.P ω * ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2
      ≤ ((C.m : ℝ) * (cHi - cLo)) ^ 2 := by
  classical
  -- pointwise bounds on the total size
  have htot_le : ∀ ω : C.Ω, (∑ i, C.size ω i) ≤ (C.m : ℝ) * cHi := by
    intro ω
    have : ∑ i : Fin C.m, C.size ω i ≤ ∑ _i : Fin C.m, cHi :=
      Finset.sum_le_sum fun i _ => (C.hsize ω i).2
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  have hle_tot : ∀ ω : C.Ω, (C.m : ℝ) * cLo ≤ ∑ i, C.size ω i := by
    intro ω
    have : ∑ _i : Fin C.m, cLo ≤ ∑ i : Fin C.m, C.size ω i :=
      Finset.sum_le_sum fun i _ => (C.hsize ω i).1
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  -- the same bounds for the mean
  have hmean_le : (∑ ω', C.P ω' * ∑ i, C.size ω' i) ≤ (C.m : ℝ) * cHi := by
    have h1 : ∑ ω', C.P ω' * (∑ i, C.size ω' i) ≤ ∑ ω', C.P ω' * ((C.m : ℝ) * cHi) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (htot_le ω) (le_of_lt (C.hP ω))
    have h2 : ∑ ω', C.P ω' * ((C.m : ℝ) * cHi) = (C.m : ℝ) * cHi := by
      rw [← Finset.sum_mul, C.hPsum, one_mul]
    linarith [h2 ▸ h1]
  have hle_mean : (C.m : ℝ) * cLo ≤ ∑ ω', C.P ω' * ∑ i, C.size ω' i := by
    have h1 : ∑ ω', C.P ω' * ((C.m : ℝ) * cLo) ≤ ∑ ω', C.P ω' * (∑ i, C.size ω' i) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hle_tot ω) (le_of_lt (C.hP ω))
    have h2 : ∑ ω', C.P ω' * ((C.m : ℝ) * cLo) = (C.m : ℝ) * cLo := by
      rw [← Finset.sum_mul, C.hPsum, one_mul]
    linarith [h2 ▸ h1]
  -- each deviation is bounded by the width of the interval
  have hdev : ∀ ω : C.Ω,
      ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2
        ≤ ((C.m : ℝ) * (cHi - cLo)) ^ 2 := by
    intro ω
    have h1 := htot_le ω
    have h2 := hle_tot ω
    have hw : (C.m : ℝ) * (cHi - cLo) = (C.m : ℝ) * cHi - (C.m : ℝ) * cLo := by ring
    have habs : |(∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i|
        ≤ (C.m : ℝ) * (cHi - cLo) := by
      rw [abs_le, hw]
      constructor <;> linarith [hmean_le, hle_mean]
    have := sq_abs ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i)
    nlinarith [abs_nonneg ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i)]
  calc ∑ ω, C.P ω * ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2
      ≤ ∑ ω, C.P ω * ((C.m : ℝ) * (cHi - cLo)) ^ 2 :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hdev ω) (le_of_lt (C.hP ω))
    _ = ((C.m : ℝ) * (cHi - cLo)) ^ 2 := by rw [← Finset.sum_mul, C.hPsum, one_mul]
