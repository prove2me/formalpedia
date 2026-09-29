-- Prove2me | solution 1 for JacSign.card_halfSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:13:26.52498+00:00
-- url     : https://prove2.me/submissions/921cfbff-1e74-4ca7-8209-9a88d10db9d9

-- Sol generated from Tropical/JacobiSignedTwoAdic.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_sum_eq_two_mul_half

/-!
# The exact 2-adic valuation of the Jacobi-signed circle count

Every observed value of the statistic is `2` times an *odd* number
(`-2, -6, 10, -10, 6, -14, -18, 22, 26, 34, ...`).  This is not a coincidence: we prove

`p ≡ 1 (mod 4) → W p ≡ 2 (mod 4)`  (`JacSign.W_mod_four`),

i.e. `v₂(W p) = 1` exactly.  The argument is a parity count over the "lower half" of the
residues: `W p = 2 S` with `S` a sum of `(p-1)/2` values in `{0, ±1}`, exactly one of which
(the term `x = 1`) vanishes, so `S ≡ (p-1)/2 - 1 ≡ 1 (mod 2)`.

Combined with the Jacobsthal identity of `JacobiSignedTwoSquares.lean` this pins down the
classical normalisation of Fermat's two-square decomposition: `p = a² + b²` with
`a = W p / 2` **odd**.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]







open JacSign in
theorem solution(hp : p ≠ 2) : 2 * ((halfSet p).card : ℤ) = (p : ℤ) - 1 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have h := sum_eq_two_mul_half p hp (fun x : ZMod p => if x = 0 then (0 : ℤ) else 1)
    (by intro x; simp [neg_eq_zero]) (by simp)
  have hleft : (∑ x : ZMod p, if x = 0 then (0 : ℤ) else 1) = (p : ℤ) - 1 := by
    rw [Finset.sum_ite]
    have hset : (univ.filter (fun x : ZMod p => ¬ x = 0)) = univ.erase 0 := by
      ext x; simp [Finset.mem_erase, and_comm]
    rw [Finset.sum_const, Finset.sum_const, hset,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    simp only [smul_zero, zero_add, nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hright : (∑ x ∈ halfSet p, if x = 0 then (0 : ℤ) else 1) = ((halfSet p).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [if_neg (Finset.mem_erase.mp hx).1]
  rw [hleft, hright] at h
  omega
