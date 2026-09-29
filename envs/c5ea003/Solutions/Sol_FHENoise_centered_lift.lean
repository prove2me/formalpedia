-- Prove2me | solution 1 for FHENoise.centered_lift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:31:18.239048+00:00
-- url     : https://prove2.me/submissions/cb7f189a-dbab-4616-8c1b-35aa3bcea21b

-- Sol generated from Cryptography/FHE/BGVInstantiation.lean
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


/-! ## 2. The BGV decoder over `ℤ` -/

variable (q t : ℕ) [NeZero q]




/-! ## 3. Concrete circuit correctness for integer BGV -/



open FHENoise in
theorem solution(q : ℕ) [NeZero q] (x : ℤ) (h : 2 * |x| < q) :
    ((x : ZMod q).valMinAbs : ℤ) = x := by
  have h1 : (((x : ZMod q).valMinAbs : ℤ) : ZMod q) = (x : ZMod q) := ZMod.coe_valMinAbs _
  have h2 : (q : ℤ) ∣ ((x : ZMod q).valMinAbs - x) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by push_cast [h1]; ring)
  have h3 := ZMod.valMinAbs_mem_Ioc (x := (x : ZMod q))
  simp only [Set.mem_Ioc] at h3
  obtain ⟨k, hk⟩ := h2
  have hq : (0 : ℤ) < q := by
    have hne : q ≠ 0 := NeZero.ne q
    positivity
  have hx1 : 2 * x < (q : ℤ) := lt_of_le_of_lt (by linarith [le_abs_self x]) h
  have hx2 : -(q : ℤ) < 2 * x := by linarith [neg_abs_le x, h]
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (q : ℤ) * k ≤ -(q : ℤ) := by nlinarith
      omega
    · have hge : (q : ℤ) ≤ (q : ℤ) * k := le_mul_of_one_le_right (le_of_lt hq) (by omega)
      omega
  rw [hk0, mul_zero] at hk
  omega
