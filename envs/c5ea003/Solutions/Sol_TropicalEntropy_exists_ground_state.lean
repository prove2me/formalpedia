-- Prove2me | solution 1 for TropicalEntropy.exists_ground_state
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:57:21.690385+00:00
-- url     : https://prove2.me/submissions/c4a84174-3623-44ca-8af8-ae5e188df088

-- Sol generated from Combinatorics/TropicalentropyDefs/TropicalEntropy_Defs.lean
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











open TropicalEntropy in
theorem solution{s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, tropSum s hs f = f i := by
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_inf' hs f
  exact ⟨i, hi, hval⟩
