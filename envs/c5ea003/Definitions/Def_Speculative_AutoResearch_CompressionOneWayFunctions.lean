-- Prove2me | Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
-- name    : Speculative_AutoResearch_CompressionOneWayFunctions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:26:49.764388+00:00
-- url     : https://prove2.me/theorems/ea5b12c5-636b-480a-9455-fb374cff7aea
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CompressionOneWayFunctions
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CompressionOneWayFunctions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CompressionOneWayFunctions.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Compression and One-Way Functions

## Overview

This file develops a fully formal, finitary account of the folklore link between
**compression** (finding short descriptions of strings) and **cryptographic
hardness** (inverting one-way functions).  It is the Phase-B/Milestone-M8
component of the research programme *Compression Beyond the Pigeonhole Bound*:
its purpose is to calibrate exactly how far randomness (and, more generally,
computational power) can push a compressor.

The development has four layers.

### 1. Description systems and the pigeonhole ceiling

A *decompressor* is any map `D : Str → α` from bit strings to objects.  The
complexity `K D y` is the length of a shortest `D`-program for `y`.  The
counting theorem `card_le_of_K_le` says: at most `2^(s+1) - 1` objects have
complexity `≤ s`.  This is the information-theoretic ceiling; no amount of
computational power moves it.

### 2. Randomness: the seed-budget theorem

`card_le_of_K_le_seeded` shows that a *seeded* (randomized) family of
decompressors indexed by a finite seed space `R` compresses at most
`|R| * (2^(s+1) - 1)` objects to `s` bits, i.e. randomness buys at most
`log₂|R| + 1` bits.  `seeded_prefix_covers` gives a matching construction
achieving exactly `log₂|R|` bits.  Together (`randomness_gain_exact`) they pin
down the worst-case value of randomness for compression: **exactly the seed
length, and no more**.

### 3. Compression search ⇋ inversion

`ShortestFinder D A` is the *compression-search task*: `A` must output a
shortest `D`-program for every describable `y` (the finitary analogue of
solving MINKT / computing `K^t` with a witness).  `Inverts f A` is the
*inversion task*.  The two are shown to be equivalent relative to any class of
algorithms closed under length guarding and bounded search:

* `shortestFinder_inverts` : compression search is at least as hard as inversion;
* `searchFinder_correct`   : inverters for the length-guarded functions
  `guardFun f l` can be combined, by a bounded linear search over the guard
  length, into a genuine shortest-program finder;
* `inversion_iff_shortest_compression` : the two tasks are equivalent for a
  `SearchClosedClass`;
* `owf_iff_compression_hard` : **one-way functions exist iff the
  compression-search problem is hard**.

### 4. Consequences for achievable worst-case bounds

`owf_description_gap` isolates the phenomenon that motivates the whole
programme: under a one-way function, there are strings whose short descriptions
*provably exist* (indeed have length bounded by an allowed resource bound) and
which *no efficient algorithm ever outputs*.  Combined with the pigeonhole
ceiling this gives the calibration statement `compression_calibration`.

All results are proved from scratch; there are no axioms and no `sorry`.
-/

namespace CompressionOWF

/-- Bit strings. -/
abbrev Str := List Bool

/-! ## Section 0: A concrete injective code for bit strings

We need the elementary fact that there are fewer than `2^(s+1)` bit strings of
length at most `s`.  Rather than importing a counting instance we build the
standard "leading one" numeral, which turns a bit string into a positive
natural number, injectively, with `natCode p < 2^(|p|+1)`. -/

/-- Binary code of a bit list as a positive natural number (leading-one convention). -/
def natCode : Str → ℕ
  | [] => 1
  | b :: t => 2 * natCode t + (if b then 1 else 0)




/-! ## Section 1: Description systems and Kolmogorov-style complexity -/

section Complexity

variable {α : Type*}

/-- `y` is describable under the decompressor `D` if some program outputs it. -/
def Describable (D : Str → α) (y : α) : Prop := ∃ p : Str, D p = y

/-- Kolmogorov-style complexity of `y` relative to the decompressor `D`:
the length of a shortest `D`-program for `y` (`0` if `y` is not describable). -/
noncomputable def K (D : Str → α) (y : α) : ℕ :=
  sInf {n | ∃ p : Str, p.length = n ∧ D p = y}






end Complexity

/-! ## Section 2: The pigeonhole bound is attained, and randomness gains exactly
the seed length -/

/-- The finite set of all bit strings of a given length. -/
def bitStrings (n : ℕ) : Finset Str :=
  Finset.image (fun v : Fin n → Bool => List.ofFn v) Finset.univ




/-- The seeded family of "prefix decompressors": the seed supplies the first
`k` bits, the program supplies the rest. -/
def prefixSys (r : Str) : Str → Str := fun p => r ++ p



/-! ## Section 3: Compression search and inversion -/

/-- `A` inverts `f`: on every value in the range of `f` it produces a preimage. -/
def Inverts (f A : Str → Str) : Prop := ∀ y : Str, Describable f y → f (A y) = y

/-- `A` solves the **compression-search problem** for the decompressor `D`: on
every describable `y` it outputs a *shortest* `D`-program for `y`. -/
def ShortestFinder (D A : Str → Str) : Prop :=
  ∀ y : Str, Describable D y → D (A y) = y ∧ (A y).length = K D y


/-- The length-guarded version of `f`: programs longer than `l` are rejected
(and echoed back with a `false` tag), accepted outputs carry a `true` tag. -/
def guardFun (f : Str → Str) (l : ℕ) : Str → Str :=
  fun p => if p.length ≤ l then true :: f p else false :: p

/-- Bounded linear search: the least `l ≤ fuel` with `P l`, computed with `fuel`
steps. -/
def leastFrom (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if P 0 then 0 else leastFrom (fun k => P (k + 1)) fuel + 1


/-- The compressor assembled from inverters `A l` for the guarded functions
`guardFun f l`: search for the least guard length that succeeds, then output the
program the corresponding inverter produced. -/
def searchFinder (f : Str → Str) (A : ℕ → Str → Str) (fuel : ℕ → ℕ) : Str → Str :=
  fun y =>
    A (leastFrom (fun l => decide (guardFun f l (A l (true :: y)) = true :: y)) (fuel y.length))
      (true :: y)


/-! ## Section 4: Classes of algorithms, one-way functions, and the equivalence -/

/-- An abstract class of algorithms, closed under the two operations used by the
reduction: length guarding, and bounded search over the guard length.  The
predicate `AllowedFuel` models the admissible resource bounds (think:
polynomials); it must contain constants and the identity and be closed under
pointwise maximum. -/
structure SearchClosedClass where
  /-- The algorithms of the class. -/
  Comp : Set (Str → Str)
  /-- The admissible resource (fuel) bounds. -/
  AllowedFuel : (ℕ → ℕ) → Prop
  allowed_const : ∀ c : ℕ, AllowedFuel (fun _ => c)
  allowed_id : AllowedFuel (fun n => n)
  allowed_max : ∀ b₁ b₂, AllowedFuel b₁ → AllowedFuel b₂ →
    AllowedFuel (fun n => max (b₁ n) (b₂ n))
  guard_mem : ∀ f ∈ Comp, ∀ l : ℕ, guardFun f l ∈ Comp
  search_mem : ∀ f ∈ Comp, ∀ A : ℕ → Str → Str, (∀ l, A l ∈ Comp) →
    ∀ b, AllowedFuel b → searchFinder f A b ∈ Comp

/-- `f` is *honest* for the class: every describable value has a program whose
length is within an admissible bound.  (Real candidate one-way functions are
honest: preimages are of polynomially related length.) -/
def HonestIn (C : SearchClosedClass) (f : Str → Str) : Prop :=
  ∃ b, C.AllowedFuel b ∧ ∀ y : Str, Describable f y → K f y ≤ b y.length


/-- `f` is a one-way function for the class `C`. -/
def OneWayIn (C : SearchClosedClass) (f : Str → Str) : Prop :=
  f ∈ C.Comp ∧ HonestIn C f ∧ ∀ A ∈ C.Comp, ¬ Inverts f A

/-- The compression-search problem for `D` is hard for the class `C`. -/
def CompressionSearchHard (C : SearchClosedClass) (D : Str → Str) : Prop :=
  D ∈ C.Comp ∧ HonestIn C D ∧ ∀ A ∈ C.Comp, ¬ ShortestFinder D A



/-! ## Section 5: Consequences for achievable worst-case bounds -/



/-- The equivalence is not vacuous: classes satisfying the closure axioms exist
(e.g. the class of *all* functions, with all fuel bounds allowed).  In that
class no one-way function exists, and — consistently with the main theorem —
every honest decompressor admits a shortest-program finder. -/
def fullClass : SearchClosedClass where
  Comp := Set.univ
  AllowedFuel := fun _ => True
  allowed_const := fun _ => trivial
  allowed_id := trivial
  allowed_max := fun _ _ _ _ => trivial
  guard_mem := fun _ _ _ => Set.mem_univ _
  search_mem := fun _ _ _ _ _ _ => Set.mem_univ _



/-! ### A class in which a one-way function genuinely exists

The equivalence would be vacuous if the closure axioms of `SearchClosedClass`
forced every function to be invertible.  They do not: the class of
length-nondecreasing algorithms is closed under guarding and bounded search, and
the tagging function `p ↦ true :: p` is one-way for it (any inverter must delete
a bit, which the class forbids).  Consequently, by `owf_iff_compression_hard`,
the compression-search problem is hard for that class as well. -/

/-- Algorithms that never shorten their input. -/
def lengthClass : SearchClosedClass where
  Comp := {g : Str → Str | ∀ p : Str, p.length ≤ (g p).length}
  AllowedFuel := fun _ => True
  allowed_const := fun _ => trivial
  allowed_id := trivial
  allowed_max := fun _ _ _ _ => trivial
  guard_mem := by
    intro f hf l p
    by_cases hp : p.length ≤ l
    · have := hf p
      simp only [guardFun, if_pos hp, List.length_cons]
      omega
    · simp [guardFun, if_neg hp]
  search_mem := by
    intro f _ A hA b _ y
    have := hA (leastFrom
      (fun l => decide (guardFun f l (A l (true :: y)) = true :: y)) (b y.length)) (true :: y)
    simp only [List.length_cons] at this
    exact le_trans (by omega) this

/-- The tagging function: prepend a `true` bit. -/
def tagTrue : Str → Str := fun p => true :: p



end CompressionOWF


