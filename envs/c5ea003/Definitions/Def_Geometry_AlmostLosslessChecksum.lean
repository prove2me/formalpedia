-- Prove2me | Definitions.Def_Geometry_AlmostLosslessChecksum
-- name    : Geometry_AlmostLosslessChecksum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:42:17.761727+00:00
-- url     : https://prove2.me/theorems/438fb941-6dec-4350-a0b2-5f7910134fed
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessChecksum
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessChecksum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessChecksum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Closing the silent-corruption loophole: a random checksum layer

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`Geometry.AlmostLosslessDecoder` proves that the scanning decoder never returns a
wrong string *provided the transmitted string is typical*.  Adversarial review
exposes the remaining loophole: an **atypical** source string `x ∉ S` can be
silently decoded to some typical `y ≠ x`, because the decoder has no way of
knowing that `x` was atypical.

Here we close that loophole with an independent random checksum
`C : α → Fin K` appended to the codeword (`log₂ K` extra bits).  The key point is
a *conditional independence* (fibrewise counting) argument: for a fixed hash
codebook `H` the candidate returned by the hash decoder is already determined,
so the checksum has only one chance in `K` of confirming it.

* `AlmostLossless.decodeChk_cost` — exact cost `|L| + 1` comparisons.
* `AlmostLossless.decodeChk_never_wrong` — typical strings are still never
  silently corrupted (deterministically).
* `AlmostLossless.silent_corruption_prob_le` — **for every source string, typical
  or not**, the probability of a silent corruption is at most `1 / K`.
-/

namespace AlmostLossless

open Finset

variable {α : Type*} [DecidableEq α] {M K : ℕ}

/-! ## 1. The checksummed scheme -/

/-- Encoder with checksum: hash plus an independent random checksum. -/
def encChk (H : α → Fin M) (C : α → Fin K) (x : α) : Fin M × Fin K := (H x, C x)

/-- Decoder with checksum: run the scanning decoder, then accept its candidate
only if the checksum matches.  The cost is one comparison more than the plain
decoder. -/
def decodeChk (L : List α) (H : α → Fin M) (C : α → Fin K) (p : Fin M × Fin K) :
    Option α × ℕ :=
  ((decode L H p.1).1.bind (fun y => if C y = p.2 then some y else none),
   (decode L H p.1).2 + 1)




/-! ## 2. The silent-corruption probability, uniformly over all sources -/

variable [Fintype α]

/-- A decoding outcome is a *silent corruption* for `x` when the decoder confidently
outputs a string different from `x`. -/
def IsSilent (o : Option α) (x : α) : Prop := o.isSome ∧ o ≠ some x

instance (o : Option α) (x : α) : Decidable (IsSilent o x) := by
  unfold IsSilent; infer_instance

/-- The set of (hash, checksum) codebook pairs that silently corrupt `x`. -/
def silentSet (L : List α) (x : α) (M K : ℕ) :
    Finset ((α → Fin M) × (α → Fin K)) :=
  univ.filter (fun p => IsSilent (decodeChk L p.1 p.2 (encChk p.1 p.2 x)).1 x)

/-- The checksum slice of the silent set above a fixed hash codebook. -/
def silentSlice (L : List α) (x : α) (H : α → Fin M) (K : ℕ) : Finset (α → Fin K) :=
  univ.filter (fun C => IsSilent (decodeChk L H C (encChk H C x)).1 x)




end AlmostLossless


