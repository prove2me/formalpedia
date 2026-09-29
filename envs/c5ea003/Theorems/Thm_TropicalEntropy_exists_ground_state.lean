-- Prove2me | Theorems.Thm_TropicalEntropy_exists_ground_state
-- name    : TropicalEntropy.exists_ground_state
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:34:27.834056+00:00
-- url     : https://prove2.me/theorems/febcffc7-fb84-4b4b-850a-e34d4ee1ed29
-- title:
--   Exists ground state
-- statement:
--   Formal statement of `TropicalEntropy.exists_ground_state` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalEntropy.exists_ground_state{s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
--       ∃ i ∈ s, tropSum s hs f = f i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/TropicalentropyDefs/TropicalEntropy_Defs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/TropicalentropyDefs/TropicalEntropy_Defs.lean#L43

-- Thm stub generated from Combinatorics/TropicalentropyDefs/TropicalEntropy_Defs.lean
import Mathlib
import Definitions.Def_Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs

/-!
# Tropical entropy: definitions

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/TropicalEntropy/Defs.lean`.  It is reconstructed here as
a self-contained development of the **zero-temperature (tropical) free energy** of
a finite system: the min-plus analogue of the partition function.

For a finite non-empty configuration set `s` with energies `f`, the tropical
partition function is `⨅_{i ∈ s} f i`, the ground-state energy.  It obeys exactly
the semiring laws of the min-plus (tropical) semiring: `min` for addition and `+`
for multiplication.

Main results:

* `TropicalEntropy.tropSum_le` / `le_tropSum` — the universal property;
* `TropicalEntropy.tropSum_shift` — additivity of a constant energy shift;
* `TropicalEntropy.tropSum_product` — **factorization over products**: the ground
  state energy of a composite system is the sum of the ground state energies of its
  parts;
* `TropicalEntropy.tropSum_square` — extensivity of the tropical free energy;
* `TropicalEntropy.tropSum_antitone` — enlarging the configuration space can only
  lower the ground state energy.
-/

open TropicalEntropy

open Finset

variable {ι κ : Type*}

theorem TropicalEntropy.exists_ground_state{s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, tropSum s hs f = f i := by sorry
