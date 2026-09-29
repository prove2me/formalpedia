-- Prove2me | Theorems.Thm_ECOC_hammingDist_lt_of_majority_favor
-- name    : ECOC.hammingDist_lt_of_majority_favor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:58.15146+00:00
-- url     : https://prove2.me/theorems/63666430-f2a1-46a7-820f-d1bb9be93969
-- title:
--   HammingDist lt of majority favor
-- statement:
--   Formal statement of `ECOC.hammingDist_lt_of_majority_favor` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ECOC.hammingDist_lt_of_majority_favor{n m : ℕ}
--       (code : Fin n → Fin m → Bool) (c c' : Fin n) (y : Fin m → Bool)
--       (hmaj : 2 * ((disagreeSet code c c').filter fun j => y j = code c j).card >
--               (disagreeSet code c c').card) :
--       hammingDist y (code c) < hammingDist y (code c') := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ECOCRobust.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ECOCRobust.lean#L195

-- Thm stub generated from Bridges/ECOCRobust.lean
import Mathlib
import Definitions.Def_Bridges_ECOCRobust
import Definitions.Def_Bridges_HammingCode
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ECOC Robustness from Coordinatewise Lipschitz Margins

This file bridges coordinatewise Lipschitz stability of score-gap classifiers to
multiclass prediction robustness under nearest-codeword (ECOC) decoding.

The key insight is that tropical Satake/Hecke score maps for GL₃ provide
Lipschitz-bounded score gaps. When these gaps have sufficient margin, coordinate
bits are certified stable under perturbation. If enough coordinates are stable,
error-correcting code distance ensures the overall multiclass prediction is invariant.

## Main results

- `bit_fixed_of_margin`: A positive score gap with margin exceeding Lipschitz perturbation
  stays positive.
- `bit_fixed_of_margin_neg`: A negative score gap with sufficient margin stays negative.
- `ecoc_robust_of_coordinate_margins`: Global ECOC robustness from coordinatewise margin
  certificates and minimum code distance.
- `ecoc_robust_of_pairwise_majority_margins`: Refined pairwise majority version avoiding
  global minimum distance.

## References

The formulation is motivated by the tropical geometry / representation theory program
connecting GL₃ Hecke algebras to robust classification via tropical Satake transforms.
-/
open Finset ECOC

open ECOC

/-! ## Coordinate-level stability from Lipschitz margins -/

/-
A positive score gap with margin exceeding `L j * r` is preserved under
any perturbation satisfying the Lipschitz bound.
-/

/-
A negative score gap with margin exceeding `L j * r` stays negative.
-/

/-! ## Predicted bit vector and bad coordinates -/



/-
Key lemma: if coordinate `j` is not bad (i.e., has sufficient margin) and
the clean prediction matches the code, then the perturbed prediction also matches.
-/

/-
The Hamming distance between the perturbed prediction and the code for class `c`
is at most the number of bad coordinates.
-/

/-! ## Main ECOC robustness theorem -/


/-! ## Pairwise majority margins -/


/-
On the disagreement set, each coordinate's Bool value equals either
`code c j` or `code c' j` (since these two differ there).
-/

/-
The disagreement set partitions into coordinates favoring `c` and those favoring `c'`.
-/

/-
On disagreement coordinates, `y j ≠ code c j` iff `y j = code c' j`.
-/

/-
If strictly more than half the disagreement coordinates favor `c`,
then `y` is strictly closer to `code c` than to `code c'`.
-/

theorem ECOC.hammingDist_lt_of_majority_favor{n m : ℕ}
    (code : Fin n → Fin m → Bool) (c c' : Fin n) (y : Fin m → Bool)
    (hmaj : 2 * ((disagreeSet code c c').filter fun j => y j = code c j).card >
            (disagreeSet code c c').card) :
    hammingDist y (code c) < hammingDist y (code c') := by sorry
