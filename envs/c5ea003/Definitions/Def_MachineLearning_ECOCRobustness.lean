-- Prove2me | Definitions.Def_MachineLearning_ECOCRobustness
-- name    : MachineLearning_ECOCRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:46.651728+00:00
-- url     : https://prove2.me/theorems/21bc82ac-c954-41c7-aaed-3c4d7afff0ba
-- title:
--   Aether Catalog definitions — MachineLearning_ECOCRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.ECOCRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/ECOCRobustness.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Certified Robustness for Multiclass ECOC Decoders

This file formalizes certified robustness guarantees for multiclass classifiers
that use Error-Correcting Output Code (ECOC) decoders, combined with
coordinatewise tropical/Lipschitz control of network scores.

## Mathematical Overview

An ECOC decoder assigns class labels by comparing a binary prediction vector
to a codebook of binary codewords via Hamming agreement. Certified robustness
requires showing that small perturbations of the input cannot change the
decoded class.

The proof proceeds in three layers:

1. **Combinatorial layer**: If fewer than half the bits on each pairwise
   disagreement set flip, the decoder output is preserved.
2. **Analytic layer**: Coordinatewise Lipschitz bounds and margin conditions
   guarantee that individual bits don't flip within a ball of radius `r`.
3. **Bridge theorem**: Combining both layers yields a decoder-level certificate
   from coordinatewise tropical margins.

## Main Definitions

* `ECOC.agreement` — Hamming agreement between a bit vector and a codeword
* `ECOC.IsUniqueDecoder` — predicate for unique decoder output
* `ECOC.bitPred` — sign-based bit prediction from real scores
* `ECOC.certRadius` — per-bit certified radius

## Main Theorems

* `ECOC.ecoc_stable_under_flip_budget` — combinatorial robustness (Theorem 1)
* `ECOC.sign_stable_of_abs_lt_margin` — analytic sign stability (Theorem 2)
* `ECOC.ecoc_decoder_robust_of_coordinate_certificates` — main bridge (Theorem 3)
* `ECOC.ecoc_decoder_robust_of_pairwise_radius_count` — certified radius corollary

## References

The tropical approach to certified robustness originates in the analysis of
ReLU networks as tropical rational maps. This formalization extends the program
to structured multiclass ECOC decoders.
-/

noncomputable section

open Finset

namespace ECOC

/-! ## Core Definitions -/

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {m : ℕ}
variable {α : Type*}

/-- Number of bit positions where `b` agrees with `code c`. -/
def agreement (code : C → Fin m → Bool) (b : Fin m → Bool) (c : C) : ℕ :=
  (Finset.univ.filter fun i => b i = code c i).card

/-- Class `c` is the unique decoder output for bit vector `b`:
    it has strictly more agreement than every other class. -/
def IsUniqueDecoder
    (code : C → Fin m → Bool) (b : Fin m → Bool) (c : C) : Prop :=
  ∀ d, d ≠ c → agreement code b c > agreement code b d

/-- Predicted bit from a real-valued score: `true` iff `0 ≤ f x i`. -/
def bitPred (f : α → Fin m → ℝ) (x : α) (i : Fin m) : Bool :=
  decide (0 ≤ f x i)

/-- Per-bit certified radius from margin and Lipschitz constant. -/
def certRadius (f : α → Fin m → ℝ) (K : Fin m → ℝ) (x : α) (i : Fin m) : ℝ :=
  |f x i| / K i

/-! ## Combinatorial ECOC Robustness (Theorem 1) -/



/-
When b₀ matches code c, disagreeing with code c on D(c,d) is the same
    as having flipped from b₀.
-/

/-
**Combinatorial ECOC Robustness Theorem (Theorem 1).**
If `b₀` matches the codeword of `c` exactly, and for every competitor `d`,
fewer than half of the bits in the disagreement set `D(c,d)` have flipped
from `b₀` to `b`, then `c` is the unique decoder output for `b`.
-/

/-! ## Analytic Sign Stability (Theorem 2) -/

section SignStability

variable [PseudoMetricSpace α]

/-
If `|a - b| < |b|`, then `a` and `b` have the same weak sign.
-/

/-
**Scalar sign stability (Theorem 2).**
If `f` is `K`-Lipschitz at `x` and `K * r < |f x|`, then the sign of `f`
is preserved for all `y` with `dist y x ≤ r`.
-/

/-
**Coordinatewise bit preservation.**
If each coordinate is Lipschitz with sufficient margin, all predicted bits
are preserved in the ball.
-/

/-
A single stable bit doesn't flip under perturbation.
-/

end SignStability

/-! ## Main Bridge Theorem (Theorem 3) -/

section MainTheorem

variable [PseudoMetricSpace α]

/-
If a bit is certified (margin > K*r) but flips, we reach a contradiction.
-/

/-
Flipped bits on the disagreement set are contained in the uncertified set.
-/

/-
**Main ECOC Robustness Theorem (Theorem 3).**
If the network output at `x` matches the codeword of class `c`, each score
coordinate is Lipschitz, and for every competing class `d`, strictly fewer
than half of the separating bits are uncertified (margin ≤ K*r), then every
perturbation within radius `r` preserves the unique decoder output `c`.

This bridges local tropical/Lipschitz control, combinatorial Hamming geometry,
and global classification stability.
-/

/-
**ECOC Robustness via Certified Radii (Corollary).**
Robustness holds whenever, for every competing class, fewer than half of the
code bits separating it from `c` have certified radius ≤ `r`.
-/

end MainTheorem

end ECOC


