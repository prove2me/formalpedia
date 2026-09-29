-- Prove2me | Theorems.Thm_ExtendedEulerianRowSum_A_row_sum
-- name    : ExtendedEulerianRowSum.A_row_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:33:36.178102+00:00
-- url     : https://prove2.me/theorems/e991c0fe-791f-4c02-a78a-a8b0c34388d6
-- title:
--   Shift-invariant row sum.
-- statement:
--   **Shift-invariant row sum.**  For every `n` and every real shift `s`, the `n`-th row
--   of the extended Eulerian numbers sums to `n!`, independently of `s`.  Specialising to
--   `s = 0` recovers the classical row-sum `â_k â¨n, kâ© = n!`.
--
--   ```lean
--   theorem ExtendedEulerianRowSum.A_row_sum(n : ℕ) (s : ℝ) :
--       ∑ k ∈ range (n + 1), A n k s = (n.factorial : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ExtendedEulerianRowSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ExtendedEulerianRowSum.lean#L140

-- Thm stub generated from Shared/ExtendedEulerianRowSum.lean
import Mathlib
import Definitions.Def_Shared_ExtendedEulerianRowSum

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

open ExtendedEulerianRowSum

theorem ExtendedEulerianRowSum.A_row_sum(n : ℕ) (s : ℝ) :
    ∑ k ∈ range (n + 1), A n k s = (n.factorial : ℝ) := by sorry
