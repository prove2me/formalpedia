-- Prove2me | Definitions.Def_Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs
-- name    : Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:55:34.629983+00:00
-- url     : https://prove2.me/theorems/c41b31ef-636b-4995-b5ff-f658baa26f08
-- title:
--   Aether Catalog definitions — Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.TropicalentropyDefs.TropicalEntropy.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/TropicalentropyDefs/TropicalEntropy_Defs.lean by skeleton subtraction
import Mathlib

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

namespace TropicalEntropy

open Finset

variable {ι κ : Type*}

/-- The **tropical partition function** (ground-state energy) of the energy
function `f` on the finite non-empty configuration set `s`. -/
noncomputable def tropSum (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ℝ := s.inf' hs f









end TropicalEntropy


