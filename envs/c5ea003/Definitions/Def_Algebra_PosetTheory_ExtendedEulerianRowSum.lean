-- Prove2me | Definitions.Def_Algebra_PosetTheory_ExtendedEulerianRowSum
-- name    : Algebra_PosetTheory_ExtendedEulerianRowSum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:48:39.524985+00:00
-- url     : https://prove2.me/theorems/0773df97-dfc9-47c8-b057-8691a9dd7d0b
-- title:
--   Aether Catalog definitions — Algebra_PosetTheory_ExtendedEulerianRowSum
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetTheory.ExtendedEulerianRowSum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetTheory/ExtendedEulerianRowSum.lean by skeleton subtraction
import Mathlib

/-!
# A shift-invariant row-sum law for the extended Eulerian numbers

## Context and the problem being posed

The catalog file `Catalog/Applications/CombFoundations.lean` (with its companion
`Catalog/Applications/ExtendedEulerian.lean`) is concerned with giving a *non-circular*
account of the **extended Eulerian numbers**

  `A n k s = ∑_{i ≤ k} (-1)^i * C(n+1, i) * (k + 1 - i - s)^n`,

a one-parameter (shift `s`) deformation of the classical Eulerian numbers `⟨n, k⟩`
(recovered at `s = 0`).  There the numbers are *defined by this closed form* and the
Eulerian recurrence is then *derived*, so that no circular "define by recurrence, prove
the closed form from the recurrence, prove the recurrence from the closed form" loop
occurs.

This file poses and settles a precise, self-contained conjecture that is **tighter in
scope** than the full recurrence and whose proof is **manifestly non-circular**: it never
invokes the recurrence at all, only the closed form and the finite–difference calculus.

**Theorem (shift-invariant row sum).**  For every `n : ℕ` and every real shift `s`,

  `∑_{k = 0}^{n} A n k s = n!`.

In particular the row sum does not depend on the shift parameter `s`; specialising to
`s = 0` recovers the classical fact that the `n`-th row of Eulerian numbers sums to `n!`
(the number of permutations of `n` letters).

**Companion theorem (boundary vanishing).**  `A n k s = 0` whenever `k ≥ n + 1`, for
every `s`.  This confines the whole row to the `n + 1` entries `k = 0, …, n`, so the
finite sum above really is the entire row.

## The technique

The "advanced combinatorial technique" driving both proofs is the **forward finite
difference operator** `Δ = fwdDiff 1` and its Mathlib API:

* the `(n+1)`-st iterated difference of a degree-`n` polynomial vanishes
  (`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`);
* the `n`-th iterated difference of `x ↦ x^n` is the constant `n!`
  (`fwdDiff_iter_eq_factorial`), together with its translation invariance
  (`fwdDiff_iter_comp_add`);
* the explicit alternating-binomial expansion of an iterated difference
  (`fwdDiff_iter_eq_sum_shift`).

The closed form `A n k s` is itself an alternating binomial sum, so it matches the
`fwdDiff` expansion after reflecting the summation index.  Summing the closed form over
the row and swapping the order of summation turns the row sum into a single iterated
forward difference of the partial-sum sequence `Qsum`, which telescopes to `x ↦ (x+1-s)^n`
and hence evaluates to `n!`.

No Eulerian recurrence is used anywhere below, so the argument is free of the circularity
discussed in `CombFoundations`.
-/

open Finset Polynomial

namespace ExtendedEulerianRowSum

/-- The **extended Eulerian numbers**, defined by their closed form.  For `s = 0` this is
the classical closed form for the Eulerian numbers `⟨n, k⟩`. -/
noncomputable def A (n k : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * ((k : ℝ) + 1 - i - s) ^ n

/-- Auxiliary partial-sum sequence `Qsum n s t = ∑_{m < t} (m + 1 - s)^n`.  Its forward
difference is `t ↦ (t + 1 - s)^n`, the key telescoping used for the row-sum theorem. -/
noncomputable def Qsum (n : ℕ) (s : ℝ) : ℕ → ℝ := fun t => ∑ m ∈ range t, ((m : ℝ) + 1 - s) ^ n








end ExtendedEulerianRowSum


