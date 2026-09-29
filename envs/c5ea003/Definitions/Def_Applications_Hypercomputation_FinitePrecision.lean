-- Prove2me | Definitions.Def_Applications_Hypercomputation_FinitePrecision
-- name    : Applications_Hypercomputation_FinitePrecision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:01.039666+00:00
-- url     : https://prove2.me/theorems/9eab4c98-565e-4298-96bc-e0c4f7ed0437
-- title:
--   Aether Catalog definitions — Applications_Hypercomputation_FinitePrecision
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Hypercomputation.FinitePrecision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Hypercomputation/FinitePrecision.lean by skeleton subtraction
import Mathlib
/-
  Hypercomputation II: physical oracles, finite precision, and the
  accidentally/essentially computable distinction
  ================================================================

  A popular route to "hypercomputation" is a *physical oracle*: a piece of the
  physical world (a voltage, a length, a real number) whose exact value happens
  to encode the answers to uncomputable questions.  We model such an oracle as an
  infinite bit stream `b : ℕ → Bool` — think of the binary expansion of the
  physical quantity being measured.

  A **measurement of finite precision `p`** can extract only the first `p` bits of
  the stream; this is captured by `readBits b p`, a list of length exactly `p`.
  Any real apparatus then feeds those finitely many bits, together with its input,
  into an ordinary effective procedure `g`.

  Main results:

  * `readBits_length` : precision `p` yields exactly `p` bits.
  * `finitePrecision_computable` : **finite precision collapses to essential
    computability.**  Whatever a finite-precision device outputs is a
    `Computable` function — the finitely many oracle bits can be hard-wired into
    the program.  This is the precise sense in which "accidentally computable"
    (helped by a physical oracle, but only finitely) equals "essentially
    computable" (Turing computable).
  * `not_computable_needs_infinite_precision` : contrapositively, no
    finite-precision device can ever reproduce an uncomputable function.
  * `halting_needs_infinite_precision` : applied to the halting predicate, *any*
    physical oracle used to decide halting must be read to unbounded precision.
    Bounded precision (equivalently, bounded energy/resolution) is provably
    insufficient — hypercomputation demands infinite precision.
-/

open Nat.Partrec Nat.Partrec.Code
open scoped Classical

namespace Applications.Hypercomputation

/-- A finite-precision measurement of the oracle stream `b`: the first `p` bits,
returned as a list of length `p`.  Increasing `p` models a more precise (more
energetic, higher-resolution) physical measurement. -/
def readBits (b : ℕ → Bool) (p : ℕ) : List Bool := (List.range p).map b


variable {α : Type*} [Primcodable α]




end Applications.Hypercomputation


