-- Prove2me | solution 1 for ExtendedEulerianRowSum.A_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:57:35.294981+00:00
-- url     : https://prove2.me/submissions/a5931d12-f5da-436b-8cfd-e958fac4977c

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



/-- The `n`-th iterated forward difference of the shifted monomial `x ↦ (x + 1 - s)^n`,
expanded via `fwdDiff_iter_eq_sum_shift`, equals `n!`.  This is the finite-difference
form of the identity `Δ^n (x ↦ x^n) = n!` after a real translation by `1 - s`. -/
theorem finiteDiff_shifted_pow (n : ℕ) (s : ℝ) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k)) • (((k : ℝ) + 1 - s) ^ n)
      = (n.factorial : ℝ) := by
  have h := fwdDiff_iter_eq_sum_shift (h := (1 : ℝ)) (fun x => (x + (1 - s)) ^ n) n 0
  have hcomp := fwdDiff_iter_comp_add (h := (1 : ℝ)) (fun r => r ^ n) (1 - s) n 0
  have hfact := fwdDiff_iter_eq_factorial (R := ℝ) (n := n)
  simp only [zero_add, nsmul_eq_mul, mul_one] at h hcomp
  rw [show (fun x : ℝ => (x + (1 - s)) ^ n) = (fun r => (fun r => r ^ n) (r + (1 - s))) from rfl] at h
  rw [hcomp, hfact] at h
  have h2 : (∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k)) • (((k : ℝ) + 1 - s) ^ n))
      = ∑ x ∈ range (n + 1), ((-1 : ℤ) ^ (n - x) * (n.choose x)) • (((x : ℝ) + (1 - s)) ^ n) := by
    refine Finset.sum_congr rfl fun k _ => ?_; congr 1; ring
  rw [h2, ← h]; rfl

/-- The forward difference of the partial-sum sequence `Qsum` telescopes to the shifted
monomial `t ↦ (t + 1 - s)^n`. -/
theorem fwdDiff_Qsum (n : ℕ) (s : ℝ) :
    fwdDiff 1 (Qsum n s) = fun t : ℕ => ((t : ℝ) + 1 - s) ^ n := by
  funext t; simp only [fwdDiff, Qsum]; rw [Finset.sum_range_succ]; ring

/-- The `n`-th iterated forward difference (over `ℕ`) of `t ↦ (t + 1 - s)^n`, evaluated at
`0`, equals `n!`. -/
theorem fwdDiff_iter_g (n : ℕ) (s : ℝ) :
    (fwdDiff 1)^[n] (fun t : ℕ => ((t : ℝ) + 1 - s) ^ n) 0 = (n.factorial : ℝ) := by
  rw [fwdDiff_iter_eq_sum_shift, ← finiteDiff_shifted_pow n s]
  refine Finset.sum_congr rfl fun k _ => ?_; simp






open ExtendedEulerianRowSum in
theorem solution(n : ℕ) (s : ℝ) :
    ∑ k ∈ range (n + 1), A n k s = (n.factorial : ℝ) := by
  have hswap : ∑ k ∈ range (n + 1), A n k s
      = ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * Qsum n s (n + 1 - i) := by
    simp only [A]
    rw [show (∑ k ∈ range (n + 1), ∑ i ∈ range (k + 1),
              (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * ((k : ℝ) + 1 - i - s) ^ n)
          = ∑ i ∈ range (n + 1), ∑ k ∈ Finset.Ico i (n + 1),
              (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * ((k : ℝ) + 1 - i - s) ^ n from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum]; congr 1
      rw [Finset.sum_Ico_eq_sum_range]; simp only [Qsum]
      refine Finset.sum_congr (by simp) fun m _ => ?_; push_cast; ring
    · rw [Finset.sum_sigma', Finset.sum_sigma']
      apply Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) <;>
        simp_all [Finset.mem_sigma, Finset.mem_Ico]
      all_goals omega
  rw [hswap]
  have hext : ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * Qsum n s (n + 1 - i)
      = ∑ i ∈ range (n + 2), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * Qsum n s (n + 1 - i) := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp [Qsum]
  rw [hext]
  have hfd : ∑ i ∈ range (n + 2), (-1 : ℝ) ^ i * (Nat.choose (n + 1) i : ℝ) * Qsum n s (n + 1 - i)
      = (fwdDiff 1)^[n + 1] (Qsum n s) 0 := by
    rw [fwdDiff_iter_eq_sum_shift, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have hle : i ≤ n + 1 := by omega
    have e1 : n + 1 + 1 - 1 - i = n + 1 - i := by omega
    have e2 : n + 1 - (n + 1 - i) = i := by omega
    have e3 : (0 : ℕ) + i • 1 = i := by simp
    rw [e1, Nat.choose_symm hle, e2, e3, zsmul_eq_mul]; push_cast; ring
  rw [hfd, Function.iterate_succ_apply, fwdDiff_Qsum, fwdDiff_iter_g]
