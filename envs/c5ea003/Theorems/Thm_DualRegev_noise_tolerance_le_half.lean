-- Prove2me | Theorems.Thm_DualRegev_noise_tolerance_le_half
-- name    : DualRegev.noise_tolerance_le_half
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:37:29.855168+00:00
-- url     : https://prove2.me/theorems/c2c14e03-3b5a-4a11-90c6-288d0b5d3ba5
-- title:
--   Universal upper bound on noise tolerance.
-- statement:
--   **Universal upper bound on noise tolerance.**  Whatever encoder
--   `enc : Bool → ℤ_q` and decoder `dec : ℤ_q → Bool` one chooses, the set of noise
--   residues decoded correctly for *both* message bits has at most `q/2` elements.
--
--   The proof is a disjointness argument: translating the correctness region by the
--   gap `enc(true) − enc(false)` produces a set disjoint from it, and translation
--   preserves cardinality.
--
--   ```lean
--   theorem DualRegev.noise_tolerance_le_half(q : ℕ) [NeZero q] (enc : Bool → ZMod q) (dec : ZMod q → Bool) :
--       2 * #{r : ZMod q | dec (enc false + r) = false ∧ dec (enc true + r) = true} ≤ q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LWE/DualRegev.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LWE/DualRegev.lean#L466

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






/-! Kernel-checked sharpness of the quarter-modulus threshold at `q = 16`: the
hypothesis `4|ν| < q` fails at `ν = ±4`, and decoding indeed breaks at `ν = +4`
while still succeeding at `ν = -4` — the asymmetry predicted by
`decodeBit_correct_iff`. -/

example : decodeBit 16 (encodeBit 16 false + ((4 : ℤ) : ZMod 16)) = true := by decide

example : decodeBit 16 (encodeBit 16 false + (((-4) : ℤ) : ZMod 16)) = false := by decide

example : decodeBit 16 (encodeBit 16 true + (((-4) : ℤ) : ZMod 16)) = true := by decide



/-! ## Section 2: The scheme -/

variable {n m q : ℕ}









/-! ## Section 3: Correctness from explicit short-vector parameters -/



/-! ## Section 4: The statistical heart of IND-CPA

The ideal Dual-Regev ciphertext is uniform, translated by the message encoding.
We prove that this translate does not depend on the message *at all*: the
translated uniform distribution on a finite abelian group is the uniform
distribution.  Hence the middle game hop is free. -/

-- open removed: section is not a namespace





/-! ## Section 5: IND-CPA for Dual-Regev -/







/-! ## Section 6: Optimality of the midpoint encoding

The correctness condition of Section 1 is not merely convenient — the midpoint
encoding together with middle-half rounding tolerates the largest possible set
of noise residues that *any* bit-encoding into `ℤ_q` can tolerate. -/

theorem DualRegev.noise_tolerance_le_half(q : ℕ) [NeZero q] (enc : Bool → ZMod q) (dec : ZMod q → Bool) :
    2 * #{r : ZMod q | dec (enc false + r) = false ∧ dec (enc true + r) = true} ≤ q := by sorry
