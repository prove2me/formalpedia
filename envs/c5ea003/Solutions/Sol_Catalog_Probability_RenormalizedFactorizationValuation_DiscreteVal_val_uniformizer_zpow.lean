-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.val_uniformizer_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:22:19.800716+00:00
-- url     : https://prove2.me/submissions/e01e8f20-3e36-4a08-8a9c-d455e3201898

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
open Catalog.Probability.RenormalizedFactorizationValuation in
theorem solution {G : Type*} [CommGroup G] (V : DiscreteVal G) (n : ℤ) :
    V.val (V.uniformizer ^ n) = n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, V.val_mul, ih, V.val_uniformizer]
  | pred k ih => rw [zpow_sub_one, V.val_mul, ih, V.val_inv, V.val_uniformizer]; ring
