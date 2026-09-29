-- Prove2me | Definitions.Def_Applications_Hypercomputation_Cardinality
-- name    : Applications_Hypercomputation_Cardinality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:06.472474+00:00
-- url     : https://prove2.me/theorems/4a40b6ab-129c-47e8-afba-0242f0bd0620
-- title:
--   Aether Catalog definitions — Applications_Hypercomputation_Cardinality
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Hypercomputation.Cardinality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Hypercomputation/Cardinality.lean by skeleton subtraction
import Mathlib
/-
  Hypercomputation III: computability is a measure-zero phenomenon
  ===============================================================

  Why is hypercomputation *needed* at all?  Because Turing computability is
  extraordinarily rare.  This file makes that precise: the Turing-computable
  Boolean functions on `ℕ` form only a *countable* set, whereas the set of *all*
  Boolean functions on `ℕ` is uncountable (of cardinality continuum).  Hence

    * uncomputable functions exist, and
    * they are in fact *uncountable* — computable functions are the exception.

  Every uncomputable function is a task that only some form of hypercomputation
  could carry out, so "almost every" decision problem lies beyond Turing power.

  Main results:

  * `computable_countable` : `{ f : ℕ → Bool // Computable f }` is `Countable`.
    Proof: each computable function is `eval` of some code (`exists_code`), and it
    is recoverable from that code, giving an injection into the countable type of
    codes.
  * `uncountable_functions` : `ℕ → Bool` is uncountable (cardinality `𝔠`).
  * `exists_uncomputable` : there is a non-computable Boolean function.
  * `uncomputable_uncountable` : the non-computable functions are uncountable.
-/

open Nat.Partrec Nat.Partrec.Code
open Encodable
open scoped Classical

namespace Applications.Hypercomputation

/-- The `ℕ →. ℕ` partial function naturally attached to a total Boolean function
`f`: it always halts, returning the encoding of `f n`. -/
noncomputable def natPR (f : ℕ → Bool) : ℕ →. ℕ := fun n => (Part.some (encode (f n)) : Part ℕ)

/-- If `f` is `Computable`, its associated partial function `natPR f` is partial
recursive in Mathlib's `Nat.Partrec` sense. -/
theorem natPR_partrec {f : ℕ → Bool} (hf : Computable f) : Nat.Partrec (natPR f) :=
  Partrec.nat_iff.1 (Computable.encode.comp hf).partrec

/-- A choice of code computing a given computable Boolean function. -/
noncomputable def toCode (f : {f : ℕ → Bool // Computable f}) : Code :=
  Classical.choose (exists_code.1 (natPR_partrec f.2))

/-- The chosen code indeed evaluates to `natPR f`. -/
theorem toCode_spec (f : {f : ℕ → Bool // Computable f}) : (toCode f).eval = natPR f.1 :=
  Classical.choose_spec (exists_code.1 (natPR_partrec f.2))

/-- Distinct computable functions get distinct codes: from a code's `eval` one
recovers the underlying Boolean function, so `toCode` is injective. -/
theorem toCode_inj : Function.Injective toCode := by
  intro f g h
  apply Subtype.ext
  funext n
  have e : natPR f.1 = natPR g.1 := by rw [← toCode_spec f, ← toCode_spec g, h]
  have h2 := congrFun e n
  simp only [natPR, Part.some_inj] at h2
  exact encode_injective h2

/-- **The computable Boolean functions are countable.**  There are only countably
many programs, hence only countably many functions any of them can compute. -/
instance computable_countable : Countable {f : ℕ → Bool // Computable f} :=
  toCode_inj.countable




end Applications.Hypercomputation


