-- Prove2me | solution 1 for CyclicTypeChannel.eq_of_mul_eq_mul_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:10:08.900112+00:00
-- url     : https://prove2.me/submissions/c661ef4a-4e23-463b-bf52-665db801a3ad

-- Sol generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `box (m*n)` as
  the product `box m ×ˢ box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/





/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/




open CyclicTypeChannel in
theorem solution{m n x x' y y' : ℕ} (h : Nat.Coprime m n) (hm : 0 < m)
    (hx : x ∣ m) (hx' : x' ∣ m) (hy : y ∣ n) (hy' : y' ∣ n) (he : x * y = x' * y') :
    x = x' ∧ y = y' := by
  have hxm : Nat.gcd (x * y) m = x := by
    rw [Nat.Coprime.gcd_mul_right_cancel x (Nat.Coprime.coprime_dvd_left hy h.symm)]
    exact Nat.gcd_eq_left hx
  have hxm' : Nat.gcd (x' * y') m = x' := by
    rw [Nat.Coprime.gcd_mul_right_cancel x' (Nat.Coprime.coprime_dvd_left hy' h.symm)]
    exact Nat.gcd_eq_left hx'
  have hxx : x = x' := by rw [← hxm, ← hxm', he]
  refine ⟨hxx, ?_⟩
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hx hm
  subst hxx
  exact Nat.eq_of_mul_eq_mul_left hxpos he
