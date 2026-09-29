-- Prove2me | solution 1 for JacSign.neg_one_notMem_halfSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:13:27.006666+00:00
-- url     : https://prove2.me/submissions/bb464a11-54f8-4dd6-8e3f-905f6aafe492

-- Sol generated from Tropical/JacobiSignedTwoAdic.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

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
theorem solution(hp : p ≠ 2) : (-1 : ZMod p) ∉ halfSet p := by
  have hprime := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left hp
  have hp3 : 3 ≤ p := by have := hprime.two_le; omega
  haveI : NeZero p := ⟨by omega⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  haveI : NeZero (1 : ZMod p) := ⟨h1⟩
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one_eq_one_mod p ▸ by
    simp [Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hv : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.val_neg_of_ne_zero (1 : ZMod p), hv1]
  intro hmem
  have := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hmem)).2
  rw [hv] at this
  omega
