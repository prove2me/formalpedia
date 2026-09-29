-- Prove2me | Definitions.Def_Cryptography_LWE_DualRegev
-- name    : Cryptography_LWE_DualRegev
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:56:21.0069+00:00
-- url     : https://prove2.me/theorems/45c03972-ee2d-4671-a840-cf73abbc2087
-- title:
--   Aether Catalog definitions — Cryptography_LWE_DualRegev
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.DualRegev`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/DualRegev.lean by skeleton subtraction
import Mathlib
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

namespace DualRegev

/-! ## Section 1: Message encoding and rounding decoding over `ZMod q` -/

/-- Encode a bit as `0` or `⌊q/2⌋` in `ℤ_q`. -/
def encodeBit (q : ℕ) (b : Bool) : ZMod q := if b then ((q / 2 : ℕ) : ZMod q) else 0

/-- Decode by rounding: return `true` exactly when the representative lies in the
middle half `[q/4, 3q/4)` of `[0, q)`. -/
def decodeBit (q : ℕ) (c : ZMod q) : Bool := decide (q ≤ 4 * c.val ∧ 4 * c.val < 3 * q)




/-! Kernel-checked sharpness of the quarter-modulus threshold at `q = 16`: the
hypothesis `4|ν| < q` fails at `ν = ±4`, and decoding indeed breaks at `ν = +4`
while still succeeding at `ν = -4` — the asymmetry predicted by
`decodeBit_correct_iff`. -/


/-! ## Section 2: The scheme -/

variable {n m q : ℕ}

/-- Reduce an integer vector modulo `q`. -/
def toZq (q : ℕ) {k : ℕ} (v : Fin k → ℤ) : Fin k → ZMod q := fun i => ((v i : ℤ) : ZMod q)

/-- **Dual-Regev key generation.**  Given the public matrix `A ∈ ℤ_q^{n×m}` and a
short integer secret key `e ∈ ℤ^m`, the public key is the syndrome `u = A·e`. -/
def publicKey (A : Matrix (Fin n) (Fin m) (ZMod q)) (e : Fin m → ℤ) : Fin n → ZMod q :=
  A *ᵥ toZq q e

/-- **Dual-Regev encryption, first component**: `c₀ = Aᵀ·s + x`. -/
def ct0 (A : Matrix (Fin n) (Fin m) (ZMod q)) (s : Fin n → ZMod q) (x : Fin m → ℤ) :
    Fin m → ZMod q :=
  Aᵀ *ᵥ s + toZq q x

/-- **Dual-Regev encryption, second component**: `c₁ = ⟨u, s⟩ + x' + encode b`. -/
def ct1 (u : Fin n → ZMod q) (s : Fin n → ZMod q) (x' : ℤ) (b : Bool) : ZMod q :=
  u ⬝ᵥ s + ((x' : ℤ) : ZMod q) + encodeBit q b

/-- **Dual-Regev decryption**: round `c₁ - ⟨e, c₀⟩`. -/
def decrypt (q : ℕ) {m : ℕ} (e : Fin m → ℤ) (c0 : Fin m → ZMod q) (c1 : ZMod q) : Bool :=
  decodeBit q (c1 - (toZq q e) ⬝ᵥ c0)




/-! ## Section 3: Correctness from explicit short-vector parameters -/



/-! ## Section 4: The statistical heart of IND-CPA

The ideal Dual-Regev ciphertext is uniform, translated by the message encoding.
We prove that this translate does not depend on the message *at all*: the
translated uniform distribution on a finite abelian group is the uniform
distribution.  Hence the middle game hop is free. -/

open LWEOperational

/-- The uniform distribution on a nonempty finite type. -/
def uniformPMF (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinitePMF Ω where
  mass _ := 1 / (Fintype.card Ω : ℝ)
  nonneg _ := by positivity
  sum_mass := by
    have hpos : (0 : ℝ) < Fintype.card Ω := by
      exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- Translation of a distribution on an additive group by a fixed element. -/
def translatePMF {G : Type*} [Fintype G] [AddGroup G] (g : G) (P : FinitePMF G) :
    FinitePMF G where
  mass y := P.mass (y - g)
  nonneg y := P.nonneg _
  sum_mass := by
    have h := Equiv.sum_comp (Equiv.subRight g) P.mass
    simp only [Equiv.subRight_apply] at h
    rw [h, P.sum_mass]



/-! ## Section 5: IND-CPA for Dual-Regev -/







/-! ## Section 6: Optimality of the midpoint encoding

The correctness condition of Section 1 is not merely convenient — the midpoint
encoding together with middle-half rounding tolerates the largest possible set
of noise residues that *any* bit-encoding into `ℤ_q` can tolerate. -/

/-- The set of noise residues on which Dual-Regev decoding is correct. -/
def GoodNoise (q : ℕ) (r : ZMod q) : Prop := 4 * r.val < q ∨ 3 * q ≤ 4 * r.val

instance (q : ℕ) (r : ZMod q) : Decidable (GoodNoise q r) := by
  unfold GoodNoise; infer_instance







end DualRegev

end

/-! ## Axiom verification -/


