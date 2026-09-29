-- Prove2me | solution 2 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.canonFam_hasProfile
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:17:57.143675+00:00
-- url     : https://prove2.me/submissions/4cc3db9a-0dad-4252-ae81-838d0d6b59ac

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
open Catalog.Probability.RenormalizedFactorizationValuation Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal Finset in
theorem solution {G : Type*} [CommGroup G] (V : DiscreteVal G) (k : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (d : ℕ → ℤ) (g : G)
    (hg : V.val g = k + ∑ i ∈ range m, d i) : HasProfile V m d (canonFam V k m d g) := by
  -- `val (π ^ n) = n`
  have hz : ∀ n : ℤ, V.val (V.uniformizer ^ n) = n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, V.val_mul, ih, V.val_uniformizer]
    | pred k ih => rw [zpow_sub_one, V.val_mul, ih, V.val_inv, V.val_uniformizer]; ring
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · unfold canonFam
    rw [if_pos hi]
    by_cases h0 : i = 0
    · -- slot `0` absorbs the discrepancy
      subst h0
      rw [if_pos rfl, V.val_mul, V.val_mul, hz, hz, hg]
      ring
    · rw [if_neg h0, one_mul, hz]
  · unfold canonFam
    rw [if_neg (by omega), if_neg (by omega), one_mul]
