-- Prove2me | Definitions.Def_MachineLearning_FreeWitnessCharacterBoundary
-- name    : MachineLearning_FreeWitnessCharacterBoundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:19:40.129588+00:00
-- url     : https://prove2.me/theorems/dedd6f74-addd-4275-86ad-2973b420cd24
-- title:
--   Aether Catalog definitions — MachineLearning_FreeWitnessCharacterBoundary
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.FreeWitnessCharacterBoundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/FreeWitnessCharacterBoundary.lean by skeleton subtraction
import Mathlib
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

namespace FreeWitness

open Finset

/-! ## Splitting weights and the multiplicativity of the aggregate -/

/-- A weight on `ℕ` **splits through CRT** at `(m, n)` if it is a product of a function
of the residue mod `m` and a function of the residue mod `n`.  This is the precise form
of "CRT-multiplicative local weight". -/
def SplitsMod {R : Type*} [CommRing R] (m n : ℕ) (f : ℕ → R) : Prop :=
  ∃ A B : ℕ → R, ∀ x, f x = A (x % m) * B (x % n)



/-! ## The rank-one obstruction -/




/-! ## Inside the class: the square-root-of-one (character) weight -/

/-- The indicator weight of the equation `x² ≡ 1 (mod N)`: the CIRC/BQF-style local
weight, in one variable. -/
def sqrtOneWeight (N : ℕ) (x : ℕ) : ℤ := if x ^ 2 % N = 1 % N then 1 else 0


/-! ## Outside the class: truncation -/

/-- The truncated ("half-plane") weight at `N = 15`: the indicator of the low half of the
residue interval.  This is the one-variable model of the non-separable cut studied in
`HalfPlaneCircleBasic.lean`. -/
def truncWeight (x : ℕ) : ℤ := if 2 * (x % 15) < 15 then 1 else 0


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

end FreeWitness


