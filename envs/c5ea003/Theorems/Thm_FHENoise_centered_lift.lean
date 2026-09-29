-- Prove2me | Theorems.Thm_FHENoise_centered_lift
-- name    : FHENoise.centered_lift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:49:19.601549+00:00
-- url     : https://prove2.me/theorems/cadd3de8-2f97-4344-a64c-cf093ac7a43d
-- title:
--   If `2|x| < q` then reducing `x` modulo `q` and taking the centered
-- statement:
--   If `2|x| < q` then reducing `x` modulo `q` and taking the centered
--   representative returns `x` exactly.  This is the reason a decryption radius of
--   `q/2` is the right notion of "decodable noise".
--
--   ```lean
--   theorem FHENoise.centered_lift(q : ℕ) [NeZero q] (x : ℤ) (h : 2 * |x| < q) :
--       ((x : ZMod q).valMinAbs : ℤ) = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/BGVInstantiation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/BGVInstantiation.lean#L31

-- Thm stub generated from Cryptography/FHE/BGVInstantiation.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_BGVInstantiation

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

open FHENoise

open Polynomial

/-! ## 1. Centered lifting -/

theorem FHENoise.centered_lift(q : ℕ) [NeZero q] (x : ℤ) (h : 2 * |x| < q) :
    ((x : ZMod q).valMinAbs : ℤ) = x := by sorry
