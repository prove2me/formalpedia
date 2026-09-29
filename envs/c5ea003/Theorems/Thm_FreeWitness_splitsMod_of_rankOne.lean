-- Prove2me | Theorems.Thm_FreeWitness_splitsMod_of_rankOne
-- name    : FreeWitness.splitsMod_of_rankOne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:21:32.710198+00:00
-- url     : https://prove2.me/theorems/834d3beb-1466-46c9-8b51-7747eda67d81
-- title:
--   The rank-one criterion is also sufficient.
-- statement:
--   **The rank-one criterion is also sufficient.**  Over a field, a nowhere-vanishing
--   weight satisfying the rank-one identity on all crossed CRT quadruples *does* split.  The
--   splitting is constructed explicitly from the two "axes" of the CRT square:
--   `A a = f (crt a 0)` and `B b = f (crt 0 b) / f 0`.  Together with
--   `rankOne_of_splitsMod` this characterises CRT-multiplicative weights exactly, so the
--   boundary of the free-witness class is decided by a four-point test.
--
--   ```lean
--   theorem FreeWitness.splitsMod_of_rankOne{K : Type*} [Field K] {m n : ℕ} (h : Nat.Coprime m n)
--       {f : ℕ → K} (h0 : f 0 ≠ 0)
--       (hrank : ∀ x y z w : ℕ, z % m = x % m → z % n = y % n → w % m = y % m → w % n = x % n →
--         f x * f y = f z * f w) :
--       SplitsMod m n f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/FreeWitnessCharacterBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/FreeWitnessCharacterBoundary.lean#L124

-- Thm stub generated from MachineLearning/FreeWitnessCharacterBoundary.lean
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

theorem FreeWitness.splitsMod_of_rankOne{K : Type*} [Field K] {m n : ℕ} (h : Nat.Coprime m n)
    {f : ℕ → K} (h0 : f 0 ≠ 0)
    (hrank : ∀ x y z w : ℕ, z % m = x % m → z % n = y % n → w % m = y % m → w % n = x % n →
      f x * f y = f z * f w) :
    SplitsMod m n f := by sorry
