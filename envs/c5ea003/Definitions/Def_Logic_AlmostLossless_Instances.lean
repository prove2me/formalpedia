-- Prove2me | Definitions.Def_Logic_AlmostLossless_Instances
-- name    : Logic_AlmostLossless_Instances
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:48:29.828699+00:00
-- url     : https://prove2.me/theorems/352ba566-897f-4af9-a8b2-eb9e2aa12578
-- title:
--   Aether Catalog definitions — Logic_AlmostLossless_Instances
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AlmostLossless.Instances`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AlmostLossless/Instances.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Instances: linear scan, bucketed scan, and a concrete `ZMod p` compressor

Two instances of `AlmostLossless.ScanScheme`:

* `AlmostLossless.linearScan` — the decoder scans the whole typical set:
  cost exactly `|T|` hash evaluations, deterministic worst case.
* `AlmostLossless.bucketed` — the codeword is a pair (bucket hash, checksum
  hash) and the decoder scans only one bucket, taken from a precomputed index
  of `T`.  Its cost when decoding a typical word `x` is exactly
  `1 + collisionCount`, and the *expected* cost over the random seed is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.avg_decodeCost_bucketed_le`): the decoder
  becomes essentially constant-time once `m₁ ≳ |T|`, while the transmitted rate
  is `log m₁ + log m₂` bits.

Finally `AlmostLossless.zmod_scheme` packages the whole pipeline over
`(ZMod p)^k` with the inner-product hash family: `k` field symbols are
compressed to *one* symbol plus a failure flag, the decoder is honest for every
seed, its cost is exactly `|T|`, and the average failure probability is at most
`ε + |T|(|T|-1)/p`.  The companion statement
`AlmostLossless.zmod_uniform_hopeless` shows this is no contradiction with the
pigeonhole bound: on the *uniform* source the very same alphabet fails with
probability at least `1 - (p+1)/p^k`.
-/

namespace AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## The linear-scan scheme -/

/-- The naive scheme: the decoder scans the entire typical set. -/
def linearScan (T : Finset S) (h : A → S → M) : ScanScheme S A M where
  typical := T
  hash := h
  cand := fun _ _ => T
  cand_subset := fun _ _ => Finset.Subset.refl T
  self_mem_cand := fun _ _ hs => hs


/-! ## The bucketed scheme -/

section Bucketed

variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]

/-- The bucketed scheme: `h₁` selects a bucket of the decoder's index of `T`
and `h₂` is a checksum used to single out the right word inside the bucket. -/
def bucketed (T : Finset S) (h₁ : A₁ → S → M₁) (h₂ : A₂ → S → M₂) :
    ScanScheme S (A₁ × A₂) (M₁ × M₂) where
  typical := T
  hash := fun a x => (h₁ a.1 x, h₂ a.2 x)
  cand := fun a m => {t ∈ T | h₁ a.1 t = m.1}
  cand_subset := fun _ _ => Finset.filter_subset _ _
  self_mem_cand := fun _ _ hs => Finset.mem_filter.2 ⟨hs, rfl⟩




end Bucketed

/-! ## A concrete compressor over `(ZMod p)^k` -/

section ZMod

variable {p k : ℕ} [Fact p.Prime]

/-- The concrete Monte-Carlo compressor: source words are `k`-symbol strings
over `ZMod p`, the shared random seed is a vector `a ∈ (ZMod p)^k` produced by a
random number generator, and the codeword is the single field element
`⟨a, x⟩` (plus an explicit failure flag). -/
def zmodScheme (T : Finset (Fin k → ZMod p)) :
    ScanScheme (Fin k → ZMod p) (Fin k → ZMod p) (ZMod p) :=
  linearScan T (dotHash p k)




end ZMod

end AlmostLossless


