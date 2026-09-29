-- Prove2me | solution 1 for Price2Adic.gaussSum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:37:30.514369+00:00
-- url     : https://prove2.me/submissions/50d7e2d2-135a-4853-8f40-20036e381bc5

-- Sol generated from Cryptography/Price2Adic/GaussDial.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_GaussDial
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# Gauss-sum magnitudes are an information-free residue dial

The experiment behind this file compared numeric quadratic Gauss sums with their closed
forms on `7625` parameter cells `(a, b, M)` and found that every `|G|`-magnitude feature
is a pure function of a residue class — on the standard lab range, literally constant.
Here that observation is proved, in the model of `Cryptography.ResidueDial.Core`.

Fix an odd prime `p`, let `χ` be the quadratic character of `ZMod p` (valued in `ℂ`) and
let `ψ` be a primitive additive character.  Then:

* `gaussSum_sq_eq` — `g² = ± p`, with the sign `+` exactly when `p ≡ 1 (mod 4)`.  The
  *sign* feature is therefore a dial of modulus `4` (`gaussSum_sq_residue_dial`).
* `norm_gaussSum` — `‖g‖ = √p`: the magnitude does not depend on `ψ` at all.
* `norm_gaussSum_mulShift` — twisting `ψ` by any unit `a ∈ (ZMod p)ˣ` leaves `‖g‖`
  unchanged.  So the magnitude, read as a function of the residue class `a`, is
  **constant**: it separates no class from any other.
* `ResidueDial.speedup_of_constant_feature` — a constant feature always induces a dial of
  density `0` or `1`, hence a speedup of exactly `1`: zero bits.
* `gaussMagnitude_dial_speedup_eq_one` — combining the two: the Gauss-magnitude dial buys
  a scan speedup of exactly `1`.  This is the "`I = 0` bits" claim, proved rather than
  measured, and it sits strictly below the universal cap `4/3` of
  `ResidueDial.dialSpeedup_le_four_thirds`.

## Lab notes (round 70, exp 548)

All `7625` cells matched the closed form (`|G| ∈ {0, √M, √(2M)}`), and on the lab range
(`p ≡ q mod 4`) the normalised magnitude was constant to machine precision, giving an
empirical mutual information of `0` bits with a residue entropy of `H = 1.000`.  The
theorems below explain why no sampling could have found anything else.
-/

open Finset

open ResidueDial



open Price2Adic

open ResidueDial

variable (p : ℕ) [Fact p.Prime]


theorem ringChar_zmod_ne_two (hp : p % 2 = 1) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

theorem quadCharC_ne_one (hp : p % 2 = 1) : quadCharC p ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).mpr
    (quadraticChar_ne_one (ringChar_zmod_ne_two p hp))

theorem quadCharC_isQuadratic : (quadCharC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _









open Price2Adic in
theorem solution(hp : p % 2 = 1) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (quadCharC p) ψ ^ 2 = if p % 4 = 1 then (p : ℂ) else -(p : ℂ) := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hg : gaussSum (quadCharC p) ψ ^ 2 = (quadCharC p) (-1) * (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_sq (quadCharC_ne_one p hp) (quadCharC_isQuadratic p) hψ
  have hneg : (quadCharC p) (-1) = ((ZMod.χ₄ (Fintype.card (ZMod p)) : ℤ) : ℂ) := by
    simp only [quadCharC, MulChar.ringHomComp_apply, eq_intCast]
    rw [quadraticChar_neg_one (ringChar_zmod_ne_two p hp)]
  rw [hg, hneg, hcard, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs with h1 h2 h3
  · simp at h1; omega
  · simp at h1; omega
  · simp
  · simp
