-- Prove2me | solution 1 for ECOC.hammingDist_lt_of_majority_favor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:05:42.853659+00:00
-- url     : https://prove2.me/submissions/91775ba4-bf8d-4a1a-b238-6e6b9193d8f5

-- Sol generated from Bridges/ECOCRobust.lean
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


open ECOC in
theorem solution{n m : ℕ}
    (code : Fin n → Fin m → Bool) (c c' : Fin n) (y : Fin m → Bool)
    (hmaj : 2 * ((disagreeSet code c c').filter fun j => y j = code c j).card >
            (disagreeSet code c c').card) :
    _root_.hammingDist y (code c) < _root_.hammingDist y (code c') := by
  -- By definition of Hamming distance, we can write
  have h_hamming_c : _root_.hammingDist y (code c) =
    ((Finset.univ \ disagreeSet code c c').filter (fun j => y j ≠ code c j)).card +
    ((disagreeSet code c c').filter (fun j => y j ≠ code c j)).card := by
      simp +decide [ _root_.hammingDist, Finset.filter_filter ];
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with j ; by_cases hj : j ∈ disagreeSet code c c' <;> aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₁ |>.1 ) |>.2 ( Finset.mem_filter.mp hx₂ |>.1 );
  have h_hamming_c' : _root_.hammingDist y (code c') =
    ((Finset.univ \ disagreeSet code c c').filter (fun j => y j ≠ code c' j)).card +
    ((disagreeSet code c c').filter (fun j => y j ≠ code c' j)).card := by
      rw [ _root_.hammingDist, ← Finset.card_union_of_disjoint ];
      · congr with j ; by_cases hj : j ∈ disagreeSet code c c' <;> aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₁ |>.1 ) |>.2 ( Finset.mem_filter.mp hx₂ |>.1 );
  -- On the complement of the disagreement set, the Hamming distances are equal.
  have h_complement : ((Finset.univ \ disagreeSet code c c').filter (fun j => y j ≠ code c j)).card =
                      ((Finset.univ \ disagreeSet code c c').filter (fun j => y j ≠ code c' j)).card := by
                        congr 1 with j ; simp +contextual [ disagreeSet ];
  have h_disagree : ((disagreeSet code c c').filter (fun j => y j ≠ code c j)).card =
                     (disagreeSet code c c').card - ((disagreeSet code c c').filter (fun j => y j = code c j)).card := by
                       rw [ tsub_eq_of_eq_add_rev ];
                       rw [ Finset.card_filter_add_card_filter_not ];
  have h_disagree' : ((disagreeSet code c c').filter (fun j => y j ≠ code c' j)).card =
                           ((disagreeSet code c c').filter (fun j => y j = code c j)).card := by
                             refine' congr_arg Finset.card ( Finset.ext fun x => _ );
                             simp +decide [ disagreeSet ];
                             cases h : code c x <;> cases h' : code c' x <;> cases h'' : y x <;> simp +decide [ h, h', h'' ];
  omega
