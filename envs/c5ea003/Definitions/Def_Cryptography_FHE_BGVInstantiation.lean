-- Prove2me | Definitions.Def_Cryptography_FHE_BGVInstantiation
-- name    : Cryptography_FHE_BGVInstantiation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:36.241135+00:00
-- url     : https://prove2.me/theorems/76ae53fe-befd-4b3a-978f-7bdda660e1e1
-- title:
--   Aether Catalog definitions — Cryptography_FHE_BGVInstantiation
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FHE.BGVInstantiation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FHE/BGVInstantiation.lean by skeleton subtraction
import Mathlib

/-!
# A non-vacuous instantiation: integer BGV with centered lifting

The correctness theorems of `NoiseGrowth` are stated for an abstract decoder
`dec` that recovers the plaintext class from any phase of gauge size below the
decoding radius `T`.  A sceptical reader should ask whether such a decoder
exists at all, or whether the hypotheses are silently vacuous.  This file
answers that: for integer BGV with ciphertext modulus `q` and plaintext modulus
`t`, the *real* decoder

`dec x = ((x mod q).valMinAbs : ZMod t)`

— reduce modulo the ciphertext modulus, lift to the centered representative,
then reduce modulo the plaintext modulus — satisfies the hypothesis with
`T = q/2`, and nothing else.

* `centered_lift` — the arithmetic heart: for `2|x| < q`, the centered
  representative of `x mod q` is `x` itself.
* `bgvDecode_eq_of_small` — the decoder hypothesis of `decrypt_evalEnc`.
* `bgv_int_correct` — the resulting fully concrete correctness statement for
  homomorphic circuit evaluation over `ℤ`.
-/

namespace FHENoise

open Polynomial

/-! ## 1. Centered lifting -/


/-! ## 2. The BGV decoder over `ℤ` -/

variable (q t : ℕ) [NeZero q]

/-- Reduce modulo the ciphertext modulus, lift to the centered representative,
reduce modulo the plaintext modulus. -/
def bgvDecode (x : ℤ) : ZMod t := (((x : ZMod q).valMinAbs : ℤ) : ZMod t)

/-- Plaintext extraction: reduction modulo the plaintext modulus. -/
def bgvPi : ℤ →+* ZMod t := Int.castRingHom (ZMod t)


/-! ## 3. Concrete circuit correctness for integer BGV -/


end FHENoise


