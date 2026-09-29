-- Prove2me | Definitions.Def_MachineLearning_PRNGSeedDetection
-- name    : MachineLearning_PRNGSeedDetection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:03.066927+00:00
-- url     : https://prove2.me/theorems/5b7ff6ea-3df4-4d7a-aa6e-0762f3796536
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGSeedDetection
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGSeedDetection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGSeedDetection.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Detecting Seed-Compressible Files and Routing Them

This file joins the two halves of the "PRNG-generated real-world data" question:
the *seed-recovery* theory of `MachineLearning.PRNGSeedRecoveryLFSR` and the
*counting limits* of `MachineLearning.PRNGCompressionBound`.

A file is modelled as `Bits N` (an `N`-bit string).  It is **`L`-seed
compressible** when some binary LFSR of order `L` — that is, `2L` bits of taps
and seed — emits it verbatim.

## Main results

* `seedCompressible_iff_decodable` — **the falsifiability gate**: a file is
  `L`-seed compressible *iff* a `2L`-bit program makes the fixed decoder
  `lfsrDecoder` output the file exactly, bit for bit.
* `KC_lfsrDecoder_le` — detection pays: such a file has description complexity
  at most `2L`, independently of its length `N`.
* `card_seedCompressible_le` — at most `4 ^ L` of the `2 ^ N` files are `L`-seed
  compressible: the detector's search space, and its false-positive budget.
* `seedCompressible_rare` — the seed-compressible fraction is `2 ^ (2L - N)`.
* `exists_not_seedCompressible` — as soon as `2L < N` the detector must reject
  something, so the classifier is not vacuous.
* `classifier_dichotomy` — for any decoder `D` at all there are files that are
  *neither* seed-compressible *nor* `d`-bit compressible by `D`: the router's
  two boxes ("seed-compressible" / "model-compressible") do not cover the space.
* `not_seedCompressible_and_hard_64` — a concrete instance of the dichotomy at
  `N = 64`, `L = 8`, `d = 4`.
* `card_seedCompressible_le_sharp` — the naive `4 ^ L` count is never tight:
  all zero-seed registers collapse to the same file.
* `isSeedCompressible_of_periodic` — a real corpus that the detector does catch:
  every `p`-periodic file is seed compressible with a `2p`-bit description.
* `detector_sound_from_2L_bits`, `lfsrBits_eq_of_agree_two_mul` — a `2L`-bit
  observation window is enough: fitting `2L` bits of an `L`-seed-compressible
  file forces exact reproduction of the whole file.

## Application keywords

PRNG detection, seed recovery, LFSR fingerprinting, Kolmogorov complexity,
compression benchmark, classifier
-/


open Finset PRNGCompression

namespace PRNGSeed

/-! ### Bits versus `GF(2)` -/

/-- The bit `b` as an element of `GF(2)`. -/
def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- An element of `GF(2)` as a bit. -/
def ofZ2 (z : ZMod 2) : Bool := decide (z = 1)


/-- The binary output stream of the order-`L` LFSR with taps `c` and seed
`init`, both given as bit vectors. -/
def lfsrBits (L : ℕ) (c init : Fin L → Bool) : ℕ → Bool := fun n =>
  ofZ2 (lfsrRun (fun i => toZ2 (c i)) (fun i => toZ2 (init i)) n)

/-! ### The detector and its decoder -/

/-- A file `w : Bits N` is `L`-seed compressible when some order-`L` binary LFSR
emits it. -/
def IsSeedCompressible (N L : ℕ) (w : Bits N) : Prop :=
  ∃ c init : Fin L → Bool, ∀ i : Fin N, w i = lfsrBits L c init (i : ℕ)

/-- The canonical seed decoder: read `L` tap bits and `L` seed bits off the
program and run the register for `N` steps. -/
def lfsrDecoder (N L : ℕ) (p : List Bool) : Bits N := fun i =>
  lfsrBits L (fun j : Fin L => p.getD (j : ℕ) false)
    (fun j : Fin L => p.getD (L + (j : ℕ)) false) (i : ℕ)

/-- The `2L`-bit program encoding taps and seed. -/
def seedProgram {L : ℕ} (c init : Fin L → Bool) : List Bool :=
  List.ofFn c ++ List.ofFn init







/-! ### How much data can possibly be seed-compressible -/

open Classical in
/-- The seed-compressible files of length `N` and order `L`. -/
noncomputable def seedCompressibleFinset (N L : ℕ) : Finset (Bits N) :=
  univ.filter (fun w => IsSeedCompressible N L w)






/-! ### A concrete corpus: periodic files are seed-compressible -/



/-! ### Sample complexity of detection over `GF(2)` -/





/-! ### Routing: the two boxes do not cover the space -/



end PRNGSeed


