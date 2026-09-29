-- Prove2me | Theorems.Thm_DualRegev_decodeBit_correct_iff
-- name    : DualRegev.decodeBit_correct_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:34:41.867465+00:00
-- url     : https://prove2.me/theorems/f54973ce-b626-4314-9dd9-35ecb7363e79
-- title:
--   Sharp rounding dichotomy.
-- statement:
--   **Sharp rounding dichotomy.**  For an even modulus `q = 2h > 0`, rounding
--   decoding recovers *both* message bits from `encode b + ν` **exactly** when the
--   residue `r = ν mod q` lies in the outer quarters `[0, q/4) ∪ [3q/4, q)`.
--
--   This is an if-and-only-if: it pins down the precise correctness region of the
--   scheme, and shows in particular that the region is not symmetric in `ν` (the
--   decoding window `[q/4, 3q/4)` is half-open, so `ν = -q/4` decodes correctly
--   while `ν = +q/4` does not).
--
--   ```lean
--   theorem DualRegev.decodeBit_correct_iff(q h : ℕ) (hq : q = 2 * h) (hh : 0 < h) (nu : ℤ) :
--       ((decodeBit q (encodeBit q false + ((nu : ℤ) : ZMod q)) = false)
--         ∧ (decodeBit q (encodeBit q true + ((nu : ℤ) : ZMod q)) = true))
--         ↔ (4 * (nu % q) < q ∨ 3 * q ≤ 4 * (nu % q)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LWE/DualRegev.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LWE/DualRegev.lean#L88

-- Thm stub generated from Cryptography/LWE/DualRegev.lean
import Mathlib
import Definitions.Def_Cryptography_LWE_DualRegev
import Definitions.Def_Cryptography_LWE_OperationalSecurity
import Definitions.Def_Cryptography_LWE_SearchDecisionCore
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Dual-Regev Encryption Scheme: Exact Correctness and IND-CPA

This module constructs the **Dual-Regev** (Gentry–Peikert–Vaikuntanathan)
public-key encryption scheme over `ℤ_q` *concretely* — as honest matrix/vector
algebra, not as an abstract interface — and proves two things about it:

1. **Exact decryption correctness.**  The decryption residual is computed on the
   nose (`dualRegev_residual`): it equals the encoded message plus the single
   integer `x' - ⟨e, x⟩`.  Correctness then follows from a genuinely proved
   rounding theorem for `ZMod q` (`decodeBit_encodeBit_add`) whenever
   `4·|x' - ⟨e, x⟩| < q`, and in particular from the explicit parameter
   condition `4·(B' + m·B_e·B_x) < q` (`dualRegev_correct_of_bounds`).

2. **IND-CPA security**, in the finite-transcript `ℓ¹` model already used by the
   catalog (`Cryptography.LWE.OperationalSecurity`).  The *statistical* half of
   the argument is proved outright: the ideal ciphertext distribution — uniform,
   translated by the message encoding — is literally independent of the message
   (`l1Gap_idealCiphertext_eq_zero`).  Hence the IND-CPA gap collapses to the sum
   of the two decisional-LWE game hops, with **no** additive slack in between
   (`dualRegev_indcpa_gap`, `dualRegev_boolean_advantage`).

## Why this is the sharp statement

The usual textbook write-up of Dual-Regev security says "the ideal game does not
depend on `b`" and moves on.  Here that step is a theorem: translation by any
group element is a measure-preserving bijection of the uniform distribution on a
finite abelian group, so the two ideal ciphertext ensembles are *equal*, giving
`ℓ¹` gap exactly `0`.  Everything else in the bound is exactly the LWE
assumption.

## Main results

* `DualRegev.decodeBit_correct_iff` — the **sharp** rounding dichotomy: decoding
  is correct for both bits exactly when the noise residue lies in the outer
  quarters `[0, q/4) ∪ [3q/4, q)`.
* `DualRegev.decodeBit_encodeBit_add` — the rounding theorem for `ZMod q`
  (`q` even): `decode (encode b + ν) = b` whenever `4|ν| < q`, a corollary of
  the dichotomy.
* `DualRegev.dualRegev_residual` — the exact decryption residual identity.
* `DualRegev.dualRegev_correct` — decryption correctness under `4|ν| < q`.
* `DualRegev.dualRegev_correct_of_bounds` — correctness from short-vector bounds.
* `DualRegev.l1Gap_translate_uniform_eq_zero` — translation invariance of the
  uniform distribution on a finite abelian group.
* `DualRegev.dualRegev_indcpa_gap` — IND-CPA gap `≤ ε₀ + ε₁`.
* `DualRegev.dualRegev_boolean_advantage` — the same bound for every
  deterministic Boolean adversary.
* `DualRegev.noise_tolerance_le_half` — **no** bit-encoding into `ℤ_q` can decode
  correctly on more than `q/2` noise residues.
* `DualRegev.dualRegev_noise_tolerance_optimal` — the midpoint encoding attains
  that bound exactly, so Dual-Regev's encoding is noise-optimal.

## References

* Gentry, Peikert, Vaikuntanathan, "Trapdoors for Hard Lattices and New
  Cryptographic Constructions", STOC 2008.
* Regev, "On Lattices, Learning with Errors, Random Linear Codes, and
  Cryptography", STOC 2005 / JACM 2009.
-/

open Finset BigOperators Matrix

noncomputable section

open DualRegev

/-! ## Section 1: Message encoding and rounding decoding over `ZMod q` -/

theorem DualRegev.decodeBit_correct_iff(q h : ℕ) (hq : q = 2 * h) (hh : 0 < h) (nu : ℤ) :
    ((decodeBit q (encodeBit q false + ((nu : ℤ) : ZMod q)) = false)
      ∧ (decodeBit q (encodeBit q true + ((nu : ℤ) : ZMod q)) = true))
      ↔ (4 * (nu % q) < q ∨ 3 * q ≤ 4 * (nu % q)) := by sorry
