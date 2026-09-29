-- Prove2me | Theorems.Thm_CyclicTypeChannel_condSProjEntropy_val_4
-- name    : CyclicTypeChannel.condSProjEntropy_val_4
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:30:04.999741+00:00
-- url     : https://prove2.me/theorems/0c0ee0c9-670a-4844-9948-253bc0fa0f5c
-- title:
--   CondSProjEntropy val 4
-- statement:
--   Formal statement of `CyclicTypeChannel.condSProjEntropy_val_4` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CyclicTypeChannel.condSProjEntropy_val_4:
--       condEnt (box 4) (sProj ∘ typePair 4) (prodRes 4)
--         = (5 / 4 : ℝ) - (3 / 16 : ℝ) * Real.logb 2 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelCap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelCap.lean#L132

-- Thm stub generated from Shared/CyclicTypeChannelCap.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
/-
# Breaking the one-bit binary-fork cap

The symmetric semiprime forks previously studied are *binary* read-outs, and a
binary symmetric fork carries at most one bit.  The splitting type of a cyclic
field is **multi-state**, and this file proves that its type-pair channel
strictly exceeds the one-bit cap for every cyclic order `n ∈ {4,6,10,12,16}`,
while the quadratic case `n = 2` sits exactly at the cap.

It also proves the two *lossiness* statements that isolate the type as the
complete object:

* the root-count read-out (`splits completely?`) is a strictly coarser channel
  than the full type, already at `n = 4` and `n = 6`;
* the split-count `s`-projection of a semiprime type pair carries strictly less
  than the full type pair.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ## 1. The type-pair channel exceeds one bit -/









/-! ## 2. The root-count read-out is strictly lossy -/





/-! ## 3. The split-count `s`-projection is strictly lossy -/

theorem CyclicTypeChannel.condSProjEntropy_val_4:
    condEnt (box 4) (sProj ∘ typePair 4) (prodRes 4)
      = (5 / 4 : ℝ) - (3 / 16 : ℝ) * Real.logb 2 3 := by sorry
