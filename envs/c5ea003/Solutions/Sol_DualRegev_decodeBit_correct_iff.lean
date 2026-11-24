-- Prove2me | solution 1 for DualRegev.decodeBit_correct_iff
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:56:32.377409+00:00
-- url     : https://prove2.me/submissions/ff450f83-f5bd-48d2-b7b2-01f9d8c3841d

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

theorem val_intCast_eq_aux (q : ℕ) [NeZero q] (t : ℤ) (h0 : 0 ≤ t) (h1 : t < q) :
    (((t : ZMod q)).val : ℤ) = t := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]

theorem solution (q h : ℕ) (hq : q = 2 * h) (hh : 0 < h) (nu : ℤ) :
    ((decodeBit q (encodeBit q false + ((nu : ℤ) : ZMod q)) = false)
      ∧ (decodeBit q (encodeBit q true + ((nu : ℤ) : ZMod q)) = true))
      ↔ (4 * (nu % q) < q ∨ 3 * q ≤ 4 * (nu % q)) := by
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  set r := nu % (q : ℤ) with hrdef
  have hr0 : 0 ≤ r := Int.emod_nonneg nu (by omega)
  have hrq : r < q := Int.emod_lt_of_pos nu hqpos
  have hcast : ((nu : ℤ) : ZMod q) = ((r : ℤ) : ZMod q) := by
    rw [ZMod.intCast_eq_intCast_iff']
    simp [hrdef, Int.emod_emod_of_dvd]
  have hq2 : q / 2 = h := by omega
  have hval : (((r : ℤ) : ZMod q).val : ℤ) = r := val_intCast_eq_aux q r hr0 hrq
  constructor
  · rintro ⟨h0, -⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    rw [encodeBit, if_neg (by simp), zero_add, hcast, decodeBit] at h0
    simp only [decide_eq_false_iff_not, not_and, not_lt] at h0
    omega
  · intro hcond
    constructor
    · rw [encodeBit, if_neg (by simp), zero_add, hcast, decodeBit]
      simp only [decide_eq_false_iff_not, not_and, not_lt]
      omega
    · rw [encodeBit, if_pos rfl, hq2, hcast, decodeBit]
      simp only [decide_eq_true_eq]
      rcases hcond with hc | hc
      · have he : ((h : ℕ) : ZMod q) + ((r : ℤ) : ZMod q) = (((h : ℤ) + r : ℤ) : ZMod q) := by
          push_cast; ring
        rw [he]
        have hv : ((((h : ℤ) + r : ℤ) : ZMod q).val : ℤ) = (h : ℤ) + r :=
          val_intCast_eq_aux q _ (by omega) (by omega)
        omega
      · have he : ((h : ℕ) : ZMod q) + ((r : ℤ) : ZMod q)
            = (((h : ℤ) + r - q : ℤ) : ZMod q) := by
          push_cast; simp
        rw [he]
        have hv : ((((h : ℤ) + r - q : ℤ) : ZMod q).val : ℤ) = (h : ℤ) + r - q :=
          val_intCast_eq_aux q _ (by omega) (by omega)
        omega

#print axioms solution
