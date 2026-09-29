-- Prove2me | Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
-- name    : Speculative_AutoResearch_CompressionLasVegasOWF
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:27:18.816409+00:00
-- url     : https://prove2.me/theorems/d0fdde57-6c7c-45dc-b2b6-630f320f85b9
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CompressionLasVegasOWF
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CompressionLasVegasOWF`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CompressionLasVegasOWF.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
/-
Copyright (c) 2025. All rights reserved.

# Las Vegas compression, average description length, and the one-way boundary

## Overview

This file continues the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: "can random number generators help?").  It builds directly
on `Speculative.AutoResearch.CompressionOneWayFunctions`, which established

* the pigeonhole ceiling `card_le_of_K_le`,
* the **seed-budget** theorem `card_le_of_K_le_seeded` (a randomized decompressor
  with seed space `R` compresses at most `|R| * (2^(s+1) - 1)` objects), and
* the equivalence `owf_iff_compression_hard` between one-way functions and
  hardness of compression search.

The seed-budget theorem charges the compressor for the *whole* seed space: it only
assumes that **some** seed works for each object.  The present file sharpens and
extends that picture in three independent directions.

### 1. It is the success *probability*, not the seed length, that is paid for

`lasVegas_sum_bound` is a double-counting theorem: summing, over a finite target
set `T`, the number of seeds that compress `y` to `s` bits gives at most
`|R| * (2^(s+1) - 1)`.  Consequences:

* `lasVegas_card_bound` : if every `y ∈ T` is compressed by at least `m` seeds
  then `m * |T| ≤ |R| * (2^(s+1) - 1)`, i.e. a Las Vegas compressor with success
  probability `δ = m/|R|` gains at most `log₂(1/δ) + 1` bits — *independently of
  how many random bits it uses*;
* `zero_error_randomness_no_gain` : a randomized compressor that must succeed for
  **every** seed gains exactly nothing (the deterministic ceiling reappears);
* `lasVegas_bound_tight` : the bound is tight within a factor `2`, witnessed by
  the seeded prefix system `prefixSeeded`, where `j` of the `i + j` seed bits are
  "used" and the success probability is exactly `2^(-j)`;
* `lasVegas_incompressible` : for every seeded family and every `k` there is a
  string of length `k + s + 1` whose success probability is below `2^(-k)`.

### 2. Average-case (Shannon-type) lower bounds from pure counting

`layer_lower_bound` is a layer-cake inequality turning any counting bound into a
bound on the *sum* of description lengths.  From it:

* `avg_description_length` : for any decompressor and any set of `2^n` describable
  objects the average description length is at least `n - 2`;
* `avg_description_length_seeded` : with `2^k` seeds the average is still at least
  `n - k - 3`.  So randomness buys at most `k + O(1)` bits *on average*, not just
  in the worst case.

### 3. Las Vegas randomness does not cross the cryptographic boundary

`tryList` is a deterministic simulation of a Las Vegas algorithm: run all seeds
from a finite list and keep the first output that verifies.  For a class closed
under this operation (`LasVegasClass`), a one-way function defeats *every* Las
Vegas algorithm **totally**:

* `owf_defeats_las_vegas` : there is a describable `y` on which **all** seeds fail;
* `owf_defeats_las_vegas_compression` : the same for seeded compression search.

Non-vacuity is checked (`lengthLVClass`, `lengthClass_las_vegas_compression_hard`):
the class of length-nondecreasing algorithms satisfies the new closure axiom and
carries a genuine one-way function.

`compression_randomness_calibration` collects the four regimes into a single
statement.

All results are proved from scratch; there are no axioms and no `sorry`.
-/

namespace CompressionLasVegas

open CompressionOWF

/-! ## Section 1: Las Vegas compression — the price of a success probability -/

section LasVegas

open scoped Classical

variable {α : Type*}

/-- The set of seeds under which `y` is compressible to `s` bits. -/
noncomputable def goodSeeds {R : Type*} [Fintype R] (D : R → Str → α) (s : ℕ) (y : α) :
    Finset R :=
  Finset.univ.filter (fun r => Describable (D r) y ∧ K (D r) y ≤ s)







end LasVegas

/-! ## Section 2: the Las Vegas bound is tight -/

section Tight

open scoped Classical


/-- The seeded prefix system: the first component of the seed is prepended to the
program, the second component is ignored (it is "wasted" randomness). -/
def prefixSeeded {j i : ℕ} (r : (Fin j → Bool) × (Fin i → Bool)) (p : Str) : Str :=
  List.ofFn r.1 ++ p



end Tight

/-! ## Section 3: average description length (Shannon bounds from counting) -/

section Average

open scoped Classical

variable {α : Type*}




/-- Complexity relative to a *seeded* family: the length of a shortest program
under the best seed. -/
noncomputable def Kseed {R : Type*} (D : R → Str → α) (y : α) : ℕ :=
  sInf {n | ∃ (r : R) (p : Str), p.length = n ∧ D r p = y}



end Average

/-! ## Section 4: Las Vegas algorithms against the cryptographic boundary -/

section Crypto

/-- Deterministic simulation of a Las Vegas algorithm: run the algorithm on every
seed in the finite list `R`, verify each candidate output, and return the first
one that verifies (echoing the input if none does).  This is the operation under
which a class must be closed for Las Vegas randomness to be simulable. -/
def tryList (f : Str → Str) (A : Str → Str → Str) (R : List Str) : Str → Str :=
  fun y =>
    match R.find? (fun r => decide (f (A r y) = y)) with
    | some r => A r y
    | none => y


/-- A class of algorithms closed under the operations of `SearchClosedClass` and,
in addition, under the Las Vegas simulation `tryList` (run finitely many seeds
and keep the first verified answer).  Every reasonable deterministic complexity
class with verification is of this kind. -/
structure LasVegasClass extends SearchClosedClass where
  /-- Closure under running finitely many seeds and keeping the first verified answer. -/
  tryList_mem : ∀ f ∈ Comp, ∀ A : Str → Str → Str, (∀ r : Str, A r ∈ Comp) →
    ∀ R : List Str, tryList f A R ∈ Comp


/-- The Las Vegas version of the compression-search task: on every describable
`y`, some seed of the finite list `R` must output a shortest `D`-program. -/
def SeededShortestFinder (D : Str → Str) (A : Str → Str → Str) (R : List Str) : Prop :=
  ∀ y : Str, Describable D y → ∃ r ∈ R, D (A r y) = y ∧ (A r y).length = K D y


/-- The closure axiom is consistent: the class of all functions satisfies it. -/
def fullLVClass : LasVegasClass where
  toSearchClosedClass := fullClass
  tryList_mem := fun _ _ _ _ _ => Set.mem_univ _

/-- The closure axiom is also satisfied by a class carrying a genuine one-way
function: length-nondecreasing algorithms.  (Verification never shortens the
input, and the fallback branch echoes it.) -/
def lengthLVClass : LasVegasClass where
  toSearchClosedClass := lengthClass
  tryList_mem := by
    intro f _ A hA R y
    cases hfind : R.find? (fun r => decide (f (A r y) = y)) with
    | none =>
        show y.length ≤ (tryList f A R y).length
        simp [tryList, hfind]
    | some r =>
        have h : y.length ≤ (A r y).length := hA r y
        show y.length ≤ (tryList f A R y).length
        simpa [tryList, hfind] using h



/-! ### Section 4b: Las Vegas compression search is *equivalent* to inversion

The previous results show that one-way functions block Las Vegas compression.
The following results close the loop: Las Vegas compression search is not merely
blocked by one-way functions, it is *equivalent* to inverting them.  Randomness
is therefore worth exactly zero at the cryptographic boundary. -/



/-- Approximate Las Vegas compression: some seed must output a program that
*decodes correctly* and is within an additive slack `g` of optimal. -/
def SeededApproxFinder (D : Str → Str) (A : Str → Str → Str) (R : List Str) (g : ℕ → ℕ) : Prop :=
  ∀ y : Str, Describable D y → ∃ r ∈ R, D (A r y) = y ∧ (A r y).length ≤ K D y + g y.length



end Crypto

/-! ## Section 5: the calibration theorem -/

section Calibration

open scoped Classical


end Calibration

/-! ## Section 6: a strict hierarchy in the seed budget -/

section Hierarchy

open scoped Classical


end Hierarchy

/-! ## Section 7: the average-case constant is sharp -/

section Sharpness

open scoped Classical

/-- All bit strings of length at most `m`. -/
def bitStringsUpTo (m : ℕ) : Finset Str := (Finset.range (m + 1)).biUnion bitStrings







end Sharpness

end CompressionLasVegas


