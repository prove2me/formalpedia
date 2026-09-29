-- Prove2me | Definitions.Def_Bridges_ECOCRobust
-- name    : Bridges_ECOCRobust
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:33.319542+00:00
-- url     : https://prove2.me/theorems/83f259f8-798e-4d98-b312-cc408330534f
-- title:
--   Aether Catalog definitions — Bridges_ECOCRobust
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ECOCRobust`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ECOCRobust.lean by skeleton subtraction
import Mathlib
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

namespace ECOC

/-! ## Coordinate-level stability from Lipschitz margins -/

/-
A positive score gap with margin exceeding `L j * r` is preserved under
any perturbation satisfying the Lipschitz bound.
-/

/-
A negative score gap with margin exceeding `L j * r` stays negative.
-/

/-! ## Predicted bit vector and bad coordinates -/

/-- The predicted bit vector: coordinate `j` predicts `true` iff `0 ≤ gap j x`. -/
noncomputable def predBits {m : ℕ} {α : Type*} (gap : Fin m → α → ℝ) (x : α) : Fin m → Bool :=
  fun j => decide (0 ≤ gap j x)

/-- The "bad" coordinates for class `c` at input `x` with perturbation radius `r`:
those whose margin does not exceed the Lipschitz perturbation budget. -/
noncomputable def badCoords
    {n m : ℕ} {α : Type*}
    (code : Fin n → Fin m → Bool)
    (gap : Fin m → α → ℝ) (L : Fin m → ℝ)
    (c : Fin n) (x : α) (r : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j =>
    if code c j then gap j x ≤ L j * r else -gap j x ≤ L j * r

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

/-- The number of disagreement coordinates where class `c` has robust margin over rival `c'`. -/
noncomputable def robustDisagreeCount
    {n m : ℕ} {α : Type*}
    (code : Fin n → Fin m → Bool)
    (gap : Fin m → α → ℝ) (L : Fin m → ℝ)
    (c : Fin n) (x : α) (r : ℝ) (c' : Fin n) : ℕ :=
  ((disagreeSet code c c').filter fun j =>
    if code c j then L j * r < gap j x else L j * r < -gap j x).card

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

/-
Robust coordinates on the disagree set will agree with `code c` after perturbation.
-/

/-
**Pairwise ECOC Robustness Theorem**: for each rival `c'`, if strictly more than
half the coordinates on which `c` and `c'` differ have certified margin, then
every admissible perturbation preserves unique nearest-codeword decoding to `c`.

This avoids introducing a global minimum distance and works with pairwise
tropical Satake margins.
-/

end ECOC


