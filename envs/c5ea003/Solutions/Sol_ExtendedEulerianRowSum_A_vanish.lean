-- Prove2me | solution 1 for ExtendedEulerianRowSum.A_vanish
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:57:35.944982+00:00
-- url     : https://prove2.me/submissions/c2f818c5-fb5d-452b-963e-afabe9b0f584

-- Sol generated from Shared/ExtendedEulerianRowSum.lean
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






/-- The `(n+1)`-st iterated forward difference of the degree-`n` polynomial `x ↦ (x - s)^n`
vanishes. -/
theorem fwdDiff_pow_vanish (n : ℕ) (s : ℝ) :
    (fwdDiff 1)^[n + 1] (fun x : ℝ => (x - s) ^ n) = 0 := by
  have hP : (fun x : ℝ => (x - s) ^ n) = (fun x => Polynomial.eval x ((X - C s) ^ n)) := by
    funext x; simp
  rw [hP]
  apply Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
  have : ((X - C s : ℝ[X]) ^ n).natDegree = n := by rw [Polynomial.natDegree_pow]; simp
  omega





open ExtendedEulerianRowSum in
theorem solution(n k : ℕ) (s : ℝ) (hk : n + 1 ≤ k) : A n k s = 0 := by
  have hsub : range (n + 2) ⊆ range (k + 1) := by
    intro x hx; simp only [Finset.mem_range] at *; omega
  have htr : A n k s
      = ∑ i ∈ range (n + 2), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * ((k : ℝ) + 1 - i - s) ^ n := by
    unfold A
    rw [← Finset.sum_subset hsub]
    intro i _hi hni
    rw [Finset.mem_range] at hni
    rw [Nat.choose_eq_zero_of_lt (show n + 1 < i by omega)]; simp
  rw [htr]
  have hval : ((fwdDiff 1)^[n + 1] (fun x : ℝ => (x - s) ^ n)) ((k : ℝ) - n) = 0 := by
    rw [fwdDiff_pow_vanish]; rfl
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.sum_range_reflect] at hval
  rw [← hval]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have hle : i ≤ n + 1 := by omega
  have e1 : n + 1 + 1 - 1 - i = n + 1 - i := by omega
  have e2 : n + 1 - (n + 1 - i) = i := by omega
  rw [e1, Nat.choose_symm hle, e2, zsmul_eq_mul]
  have hbase : ((k : ℝ) - n) + (n + 1 - i) • (1 : ℝ) = (k : ℝ) + 1 - i := by
    rw [nsmul_eq_mul, Nat.cast_sub hle]; push_cast; ring
  rw [hbase]; push_cast; ring
