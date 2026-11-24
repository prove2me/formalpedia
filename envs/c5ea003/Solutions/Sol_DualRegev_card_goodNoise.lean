-- Prove2me | solution 1 for DualRegev.card_goodNoise
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:56:34.583171+00:00
-- url     : https://prove2.me/submissions/2c955a8a-b3ca-4580-ad00-75e963cae429

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

theorem goodNoise_shift_aux (q h : ℕ) [NeZero q] (hq : q = 2 * h) (hh : 0 < h) (r : ZMod q) :
    GoodNoise q (r + ((h : ℕ) : ZMod q)) ↔ ¬ GoodNoise q r := by
  have hvr : r.val < q := ZMod.val_lt r
  have hval : (r + ((h : ℕ) : ZMod q)).val = (r.val + h) % q := by
    rw [ZMod.val_add, ZMod.val_cast_of_lt (by omega)]
  unfold GoodNoise
  rw [hval]
  rcases lt_or_ge (r.val + h) q with hc | hc
  · rw [Nat.mod_eq_of_lt hc]; omega
  · rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]; omega

theorem shift_involutive_aux (q h : ℕ) [NeZero q] (hq : q = 2 * h) (r : ZMod q) :
    r + ((h : ℕ) : ZMod q) + ((h : ℕ) : ZMod q) = r := by
  have hz : ((h : ℕ) : ZMod q) + ((h : ℕ) : ZMod q) = 0 := by
    have hs : ((h : ℕ) : ZMod q) + ((h : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) := by
      rw [hq]; push_cast; ring
    rw [hs, ZMod.natCast_self]
  rw [add_assoc, hz, add_zero]

theorem solution (q h : ℕ) [NeZero q] (hq : q = 2 * h) (hh : 0 < h) :
    2 * #{r : ZMod q | GoodNoise q r} = q := by
  have hbij : #{r : ZMod q | GoodNoise q r} = #{r : ZMod q | ¬ GoodNoise q r} := by
    refine Finset.card_nbij' (fun r => r + ((h : ℕ) : ZMod q))
      (fun r => r + ((h : ℕ) : ZMod q)) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hr ⊢
      intro hcon
      exact ((goodNoise_shift_aux q h hq hh r).mp hcon) hr
    · intro r hr
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hr ⊢
      exact (goodNoise_shift_aux q h hq hh r).mpr hr
    · intro r _; exact shift_involutive_aux q h hq r
    · intro r _; exact shift_involutive_aux q h hq r
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod q))) (GoodNoise q)
  have heta : #(Finset.filter (GoodNoise q) Finset.univ) = #{r : ZMod q | GoodNoise q r} := rfl
  rw [Finset.card_univ, ZMod.card, ← hbij, heta] at htot
  omega

#print axioms solution
