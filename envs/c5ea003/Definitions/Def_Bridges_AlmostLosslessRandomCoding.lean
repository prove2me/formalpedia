-- Prove2me | Definitions.Def_Bridges_AlmostLosslessRandomCoding
-- name    : Bridges_AlmostLosslessRandomCoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:39.225096+00:00
-- url     : https://prove2.me/theorems/0c31f633-70bb-4117-b92c-ef84d122ebb1
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessRandomCoding
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessRandomCoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessRandomCoding.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression II: Random Coding with a Certified Decoder

## Bridge: Universal hashing (algebra) ↔ Shannon random coding (probability)
##         ↔ Verified algorithmics (exact decoder cost)

Shannon's random-coding argument is usually stated with an *unbounded* random
codebook and an existential (non-constructive) decoder.  Here everything is
finite, explicit and cost-instrumented:

* the "random codebook" is a **2-universal hash family** `H : Fin K → α → Fin M`
  (`Universal2`), so the randomness is a single key `k ∈ Fin K`;
* the decoder `decodeList` scans an explicit codebook list `l` and answers
  `some x` **only** when the match is unique;
* the scan is instrumented (`scanCost`) so the decoding cost is *proved*, not
  estimated: exactly `l.length` hash evaluations per query.

Main results:

* `sum_collision_mass_le` — the averaging (first-moment) identity behind random
  coding, in the exact form `M · Σₖ P(collision) ≤ K · |S| · P(A)`;
* `exists_good_key` — derandomized existence of a single good key;
* `decodeList_eq_some_of_unique`, `not_silentError_of_mem` — the decoder never
  corrupts a codebook symbol silently;
* `exists_almost_lossless_scheme` — **the deliverable**: a key `k` such that the
  scheme fails with probability `≤ δ + |S|/M`, corrupts silently with
  probability `≤ |S|/M`, and costs exactly `|S|` steps per decode;
* `converse_flat_source` — the matching converse, giving a rate gap independent
  of the source size.

## Impact: almost_lossless_achievability, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

namespace AlmostLossless

/-! ## Section 1: Universal hash families and collisions -/

section Universal

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- A **2-universal** family of hash functions: for any two distinct source
symbols, at most a `1/M` fraction of the keys make them collide.  (Stated
multiplicatively to avoid division.) -/
def Universal2 (H : Fin K → α → Fin M) : Prop :=
  ∀ x y : α, x ≠ y →
    ((Finset.univ.filter (fun k => H k x = H k y)).card : ℝ) * M ≤ K

/-- The set of codebook entries other than `x` that collide with `x`. -/
def collisionSet (H : Fin K → α → Fin M) (k : Fin K) (S : Finset α) (x : α) :
    Finset α :=
  (S.erase x).filter (fun y => H k y = H k x)

/-- `x` collides with the codebook `S` under key `k`. -/
def Collides (H : Fin K → α → Fin M) (k : Fin K) (S : Finset α) (x : α) : Prop :=
  (collisionSet H k S x).Nonempty

instance (H : Fin K → α → Fin M) (k : Fin K) (S : Finset α) :
    DecidablePred (Collides H k S) := fun _ => Finset.decidableNonempty


/-- The set of keys under which `x` collides with the codebook. -/
def badKeys (H : Fin K → α → Fin M) (S : Finset α) (x : α) : Finset (Fin K) :=
  Finset.univ.filter (fun k => Collides H k S x)


/-! ## Section 2: The first-moment (random coding) bound -/



end Universal

/-! ## Section 3: The cost-instrumented decoder -/

section Decoder

variable {α : Type*} {M : ℕ}

/-- A single left-to-right scan of the codebook list, returning the list of
matches together with the **exact number of hash evaluations performed**. -/
def scanCost (h : α → Fin M) (i : Fin M) : List α → List α × ℕ
  | [] => ([], 0)
  | y :: ys =>
      let p := scanCost h i ys
      (if h y = i then y :: p.1 else p.1, p.2 + 1)



/-- The decoder: answer `some y` **only** when the scan produced a unique match,
otherwise abstain.  Abstention is the mechanism that prevents silent
corruption of codebook symbols. -/
def decodeList (h : α → Fin M) (l : List α) (i : Fin M) : Option α :=
  match (scanCost h i l).1 with
  | [y] => some y
  | _ => none






end Decoder

/-! ## Section 4: The almost-lossless scheme and its guarantees -/

section Scheme

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- The compression scheme built from a hash function and a codebook list:
encode by hashing, decode by a unique-match scan. -/
def hashScheme (l : List α) (h : α → Fin M) : Scheme α (Fin M) where
  enc := h
  dec := decodeList h l






end Scheme

/-! ## Section 5: The matching converse for a flat (typical) source -/

section Converse

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] {Code : Type*} [Fintype Code]


end Converse

/-! ## Section 6: The two-sided rate theorem -/

section Sandwich

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] {K M : ℕ}


end Sandwich

end AlmostLossless


