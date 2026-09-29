-- Prove2me | solution 1 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.isTopSet_affine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:28:59.146539+00:00
-- url     : https://prove2.me/submissions/721af385-2752-43c1-955f-43e2bffd69fa

import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
open Catalog.Combinatorics.HybridEvictionAdditiveLaw in
theorem solution {ι : Type*} (s : ι → ℝ) {c d : ℝ} (hc : 0 < c) (B : ℕ) (S : Finset ι) :
    IsTopSet (fun i => c * s i + d) B S ↔ IsTopSet s B S := by
  -- a positive affine rescaling preserves the order of scores
  have key : ∀ i j, c * s j + d ≤ c * s i + d ↔ s j ≤ s i := by
    intro i j
    constructor
    · intro h
      have : c * s j ≤ c * s i := by linarith
      exact le_of_mul_le_mul_left this hc
    · intro h
      have := mul_le_mul_of_nonneg_left h hc.le
      linarith
  unfold IsTopSet
  constructor
  · rintro ⟨hcard, hS⟩
    exact ⟨hcard, fun i hi j hj => (key i j).mp (hS i hi j hj)⟩
  · rintro ⟨hcard, hS⟩
    exact ⟨hcard, fun i hi j hj => (key i j).mpr (hS i hi j hj)⟩
