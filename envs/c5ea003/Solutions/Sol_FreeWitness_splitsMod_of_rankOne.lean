-- Prove2me | solution 1 for FreeWitness.splitsMod_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:31:56.39889+00:00
-- url     : https://prove2.me/submissions/db143054-32a5-44bb-b72f-42878e25c092

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
theorem solution{K : Type*} [Field K] {m n : ℕ} (h : Nat.Coprime m n)
    {f : ℕ → K} (h0 : f 0 ≠ 0)
    (hrank : ∀ x y z w : ℕ, z % m = x % m → z % n = y % n → w % m = y % m → w % n = x % n →
      f x * f y = f z * f w) :
    SplitsMod m n f := by
  set crt : ℕ → ℕ → ℕ := fun a b => (Nat.chineseRemainder h a b : ℕ)
  have hcrt1 : ∀ a b, crt a b % m = a % m := fun a b =>
    (Nat.chineseRemainder h a b).2.1
  have hcrt2 : ∀ a b, crt a b % n = b % n := fun a b =>
    (Nat.chineseRemainder h a b).2.2
  refine ⟨fun a => f (crt a 0), fun b => f (crt 0 b) / f 0, ?_⟩
  intro x
  have hz1 : crt (x % m) 0 % m = x % m := by rw [hcrt1, Nat.mod_mod_of_dvd _ dvd_rfl]
  have hz2 : crt (x % m) 0 % n = 0 % n := hcrt2 _ _
  have hw1 : crt 0 (x % n) % m = 0 % m := hcrt1 _ _
  have hw2 : crt 0 (x % n) % n = x % n := by rw [hcrt2, Nat.mod_mod_of_dvd _ dvd_rfl]
  have key := hrank x 0 (crt (x % m) 0) (crt 0 (x % n)) hz1 hz2 hw1 hw2
  rw [← mul_div_assoc, eq_div_iff h0]
  exact key
