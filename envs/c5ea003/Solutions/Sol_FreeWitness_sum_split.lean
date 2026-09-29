-- Prove2me | solution 1 for FreeWitness.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:31:57.364067+00:00
-- url     : https://prove2.me/submissions/bb8eb11d-80be-4b11-bfe7-bd86c8bffd08

-- Sol generated from MachineLearning/FreeWitnessCharacterBoundary.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessCharacterBoundary
import Definitions.Def_MachineLearning_FreeWitnessSigmaK

/-!
# The characters-only boundary: which weights actually split through CRT

§3 of `16_FreeWitness_Classification.md` asserts a boundary for the free-witness
mechanism: the family works because its local weights are *character-like*
(CRT-multiplicative), and other weights — the paper cites truncations and exponential
phase functions — fall outside it.  This file makes that boundary a theorem, and in the
process corrects the paper's justification for the phase case.

**Layer 1 of the classification, proved.**  A weight that splits as
`f x = A (x % m) · B (x % n)` has an aggregate that is a product:
`∑_{x < m n} f x = (∑_{a < m} A a)(∑_{b < n} B b)` for coprime `m, n`
(`sum_split`, `sum_eq_mul_of_splitsMod`).  This is the exact statement "CRT-separable
domain + CRT-multiplicative weight ⇒ the count factors".

**A necessary condition, hence a falsification tool.**  Splitting is a *rank-one*
condition on the CRT square: whenever `z` and `w` carry the crossed residues of `x` and
`y`, one must have `f x · f y = f z · f w` (`rankOne_of_splitsMod`).  This is checkable
on four points, and it is the sharpest elementary obstruction available.

Over a field the criterion is *exact*: `splitsMod_iff_rankOne` shows that for a
nowhere-vanishing weight, splitting through CRT is equivalent to the four-point rank-one
identity, the splitting being reconstructed from the two axes of the CRT square.

**The boundary, both sides.**
* `sqrtOneWeight_splits` — the square-root-of-one indicator (the CIRC/BQF-style
  character weight) does split, for every coprime pair.
* `truncWeight_not_splits` — the *truncated* (half-plane) weight
  `x ↦ [2 (x % 15) < 15]` does **not** split at `(3, 5)`: rank-one already fails on the
  quadruple `0, 1, 6, 10`.  So truncation genuinely leaves the class, which is the
  formal counterpart of the catalog's `halfPlaneCount_not_multiplicative`.
* `phase_index_splits`, `twist_depends_on_comodulus` — the honest version of the phase
  discussion.  Exponential phases `e(x / mn)` *do* split through CRT: Bézout gives
  `x = u n x + v m x`, so `e(x/(mn)) = e(u x/m) · e(v x/n)` exactly.  What fails is not
  the splitting but the *locality*: the twist `u ≡ n⁻¹ (mod m)` depends on the **other**
  modulus, so the local factor is not a function of one prime alone
  (`(3 : ZMod 7)⁻¹ = 5` but `(5 : ZMod 7)⁻¹ = 3`, and the two induced local weights
  differ).  This is why phase witnesses are not free witnesses in the sense of the
  classification, and it is a different reason from the one stated in the paper.
-/

open FreeWitness

open Finset

/-! ## Splitting weights and the multiplicativity of the aggregate -/




/-! ## The rank-one obstruction -/




/-! ## Inside the class: the square-root-of-one (character) weight -/



/-! ## Outside the class: truncation -/



/-! ## The phase boundary: splitting holds, locality fails -/




/-! ### Lab notes (cycle 3)

CRT square for `15 = 3 · 5`, entries `x` indexed by `(x mod 3, x mod 5)`:

```
        b=0  b=1  b=2  b=3  b=4
 a=0 |   0    6   12    3    9
 a=1 |  10    1    7   13    4
 a=2 |   5   11    2    8   14
```
Truncation weight `[2x < 15]` on this square:

```
        b=0  b=1  b=2  b=3  b=4
 a=0 |   1    1    0    1    0
 a=1 |   0    1    1    0    1
 a=2 |   1    0    1    0    0
```
Rank-one test on the top-left 2×2 block: `1·1 = 1` but `1·0 = 0` — fails, so the
truncated weight is not a product of local weights.  The same square for the weight
`[x² ≡ 1 mod 15]` is the outer product of `[a² ≡ 1 mod 3]` and `[b² ≡ 1 mod 5]`.
-/

example : truncWeight 0 * truncWeight 1 ≠ truncWeight 6 * truncWeight 10 := by
  norm_num [truncWeight]

example : sqrtOneWeight 15 4 = 1 ∧ sqrtOneWeight 15 7 = 0 := by
  norm_num [sqrtOneWeight]


open FreeWitness in
theorem solution{m n : ℕ} (h : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n)
    (A B : ℕ → ℤ) :
    ∑ x ∈ range (m * n), A (x % m) * B (x % n)
      = (∑ a ∈ range m, A a) * (∑ b ∈ range n, B b) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun x => (x % m, x % n))
    (j := fun p => (Nat.chineseRemainder h p.1 p.2 : ℕ) % (m * n)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hn⟩
  · intro p _
    exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hm hn))
  · -- `j (i x) = x`: CRT uniqueness below `m n`
    intro x hx
    have hxlt : x < m * n := Finset.mem_range.mp hx
    set k := (Nat.chineseRemainder h (x % m) (x % n) : ℕ) with hk
    have hk1 : k ≡ x % m [MOD m] := (Nat.chineseRemainder h (x % m) (x % n)).2.1
    have hk2 : k ≡ x % n [MOD n] := (Nat.chineseRemainder h (x % m) (x % n)).2.2
    have hx1 : k ≡ x [MOD m] := by
      have : x % m ≡ x [MOD m] := Nat.mod_modEq x m
      exact hk1.trans this
    have hx2 : k ≡ x [MOD n] := by
      have : x % n ≡ x [MOD n] := Nat.mod_modEq x n
      exact hk2.trans this
    have hmn : k ≡ x [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hx1, hx2⟩
    show k % (m * n) = x
    calc k % (m * n) = x % (m * n) := hmn
      _ = x := Nat.mod_eq_of_lt hxlt
  · -- `i (j p) = p`
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    set k := (Nat.chineseRemainder h p.1 p.2 : ℕ) with hk
    have hk1 : k ≡ p.1 [MOD m] := (Nat.chineseRemainder h p.1 p.2).2.1
    have hk2 : k ≡ p.2 [MOD n] := (Nat.chineseRemainder h p.1 p.2).2.2
    have e1 : k % (m * n) % m = p.1 := by
      rw [Nat.mod_mod_of_dvd _ ⟨n, rfl⟩]
      calc k % m = p.1 % m := hk1
        _ = p.1 := Nat.mod_eq_of_lt hp.1
    have e2 : k % (m * n) % n = p.2 := by
      rw [Nat.mod_mod_of_dvd _ ⟨m, mul_comm m n⟩]
      calc k % n = p.2 % n := hk2
        _ = p.2 := Nat.mod_eq_of_lt hp.2
    exact Prod.ext e1 e2
  · intro x _
    rfl
