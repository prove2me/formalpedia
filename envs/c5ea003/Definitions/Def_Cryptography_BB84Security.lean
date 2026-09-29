-- Prove2me | Definitions.Def_Cryptography_BB84Security
-- name    : Cryptography_BB84Security
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:03:06.090622+00:00
-- url     : https://prove2.me/theorems/506bc008-fc8c-4a03-b967-3fea6571b8fc
-- title:
--   Aether Catalog definitions — Cryptography_BB84Security
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BB84Security`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BB84Security.lean by skeleton subtraction
import Mathlib

/-!
# A finite BB84 security core

This file formalizes a self-contained chain of nontrivial finite results underlying BB84:

* preparation and measurement in matching BB84 bases is perfectly correct;
* measuring in the conjugate basis is uniform;
* an intercept/resend attack causes error probability `1/4` on sifted bits;
* a standard universal₂-hashing failure bound is nonnegative, decreases with every
  added hash bit, and is exactly exponentially small.

The attack theorem is an exact finite calculation.  The final chain isolates the
arithmetic step used after a universal₂ collision argument has supplied a bound of
`2⁻ʳ`.  A full security theorem against arbitrary quantum side information, and a
proof of the asymptotic 11% threshold, require substantially more operator, entropy,
and probability infrastructure; neither stronger claim is made here.
-/

namespace BB84

inductive Bit where
  | zero
  | one
  deriving DecidableEq, Fintype, Repr

inductive Basis where
  | computational
  | diagonal
  deriving DecidableEq, Fintype, Repr


/-- Probability that measuring an ideal BB84 state gives a requested output bit. -/
def measurementProbability (preparedBasis measuredBasis : Basis)
    (preparedBit outputBit : Bit) : ℚ :=
  if preparedBasis = measuredBasis then
    if preparedBit = outputBit then 1 else 0
  else 1 / 2



/-- Error probability conditioned on Alice and Bob using the same basis, when Eve
intercepts in `eveBasis`, measures, and resends her result. -/
def interceptResendError (aliceBasis eveBasis : Basis) : ℚ :=
  if aliceBasis = eveBasis then 0 else 1 / 2




/-- The standard upper bound after `rounds` independent universal₂ hash checks. -/
def privacyFailureBound (rounds : ℕ) : ℚ := (1 / 2) ^ rounds







end BB84


