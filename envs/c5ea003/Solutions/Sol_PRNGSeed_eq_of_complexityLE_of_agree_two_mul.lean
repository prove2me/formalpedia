-- Prove2me | solution 1 for PRNGSeed.eq_of_complexityLE_of_agree_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:53:30.053365+00:00
-- url     : https://prove2.me/submissions/be771a55-8261-48a1-8f2d-0d78c013ba8f

-- Sol generated from MachineLearning/PRNGBerlekampMassey.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
import Theorems.Thm_PRNGSeed_charPoly_recOfPoly
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Why `2L` Samples Suffice: the Foundation of Berlekamp–Massey

`MachineLearning.PRNGSeedRecoveryLFSR` shows that a stream obeying a *known*
order-`L` recurrence is reproduced exactly from `L` symbols.  Detection is
harder: the taps are unknown, so different candidate registers compete.  This
file proves the theorem that makes fingerprinting possible at all:

> two streams of linear complexity at most `L` that agree on the first `2L`
> symbols agree **forever**.

Hence a `2L`-symbol observation window is enough to identify a stream inside the
complexity-`≤ L` class — the correctness guarantee behind Berlekamp–Massey, and
the reason a seed-recovery pipeline can commit after seeing `2L` samples.

## Method

The shift operator `shift : (ℕ → F) →ₗ[F] (ℕ → F)` turns `ℕ → F` into an
`F[X]`-module.  A stream is a solution of a recurrence exactly when the
recurrence's characteristic polynomial annihilates it (`isSolution_iff_aeval`).
Annihilators multiply, so the difference of two complexity-`≤ L` streams is
annihilated by a *monic degree-`2L`* polynomial, i.e. it is a solution of some
order-`2L` recurrence; vanishing on `2L` consecutive symbols then forces it to
vanish identically.

We reuse Mathlib's `LinearRecurrence` API (`charPoly`, `mkSol`,
`sol_eq_of_eq_init`) and bridge it to the `IsLinRec` predicate of the LFSR file.

## Main results

* `isSolution_iff_aeval` — solution ⟺ annihilated by the characteristic
  polynomial acting through the shift operator.
* `charPoly_recOfPoly` — every monic polynomial is the characteristic polynomial
  of an explicit linear recurrence.
* `complexityLE_add`, `complexityLE_sub` — linear complexity is subadditive.
* `eq_zero_of_complexityLE_of_init_zero` — a complexity-`m` stream vanishing on
  `m` initial symbols vanishes identically.
* `eq_of_complexityLE_of_agree_two_mul` — **`2L` samples determine the stream.**
* `complexity_detector_sound` — a detector that fits any order-`L` register to
  the first `2L` symbols has, in fact, fitted the entire stream.
* `distinct_lfsr_streams_differ_early` — two order-`L` registers with different
  output streams already differ inside the first `2L` symbols, so the
  observation window cannot be shortened below `2L` without ambiguity.

## Application keywords

Berlekamp–Massey, linear complexity, shift operator, characteristic polynomial,
PRNG fingerprinting, seed recovery, sample complexity
-/


open Finset Polynomial

open PRNGSeed

variable {F : Type*} [CommRing F]

/-! ### The shift operator and the `F[X]`-module structure on streams -/


@[simp] lemma shift_apply (x : ℕ → F) (n : ℕ) : shift x n = x (n + 1) := rfl

@[simp] lemma shift_pow_apply (k : ℕ) (x : ℕ → F) (n : ℕ) :
    ((shift : (ℕ → F) →ₗ[F] (ℕ → F)) ^ k) x n = x (n + k) := by
  induction k generalizing x n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih (shift x) n, shift_apply]
    simp [Nat.add_assoc]

/-- Acting with a monomial is a scaled shift. -/
lemma aeval_shift_monomial (k : ℕ) (a : F) (x : ℕ → F) (n : ℕ) :
    (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) (Polynomial.monomial k a)) x n
      = a * x (n + k) := by
  rw [Polynomial.aeval_monomial]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- The characteristic polynomial of a linear recurrence, acting through the
shift operator, measures the failure of a stream to obey the recurrence. -/
lemma aeval_charPoly_apply (E : LinearRecurrence F) (x : ℕ → F) (n : ℕ) :
    (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) E.charPoly) x n
      = x (n + E.order) - ∑ i : Fin E.order, E.coeffs i * x (n + (i : ℕ)) := by
  rw [LinearRecurrence.charPoly, map_sub, map_sum]
  simp only [LinearMap.sub_apply, Pi.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
    aeval_shift_monomial, one_mul]

/-- **Streams as an `F[X]`-module.**  A stream obeys a linear recurrence exactly
when the characteristic polynomial of that recurrence annihilates it. -/
theorem isSolution_iff_aeval (E : LinearRecurrence F) (x : ℕ → F) :
    E.IsSolution x ↔
      (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) E.charPoly) x = 0 := by
  constructor
  · intro h
    funext n
    rw [aeval_charPoly_apply, h n, sub_self]
    rfl
  · intro h n
    have hn := congrFun h n
    rw [aeval_charPoly_apply] at hn
    exact sub_eq_zero.mp (by simpa using hn)

/-! ### Recurrences from monic polynomials -/



/-! ### Linear complexity and the `2L` sample bound -/



/-- A stream annihilated by a monic degree-`m` polynomial has complexity at most
`m`. -/
theorem complexityLE_of_annihilated {m : ℕ} {r : F[X]} {z : ℕ → F} (hr : r.Monic)
    (hd : r.natDegree = m)
    (hz : (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) r) z = 0) :
    ComplexityLE m z := by
  refine ⟨(recOfPoly m r).coeffs, ?_⟩
  have hsol : (recOfPoly m r).IsSolution z := by
    rw [isSolution_iff_aeval, charPoly_recOfPoly hr hd]
    exact hz
  exact hsol

/-- A stream of complexity at most `m` whose first `m` symbols vanish is
identically zero. -/
theorem eq_zero_of_complexityLE_of_init_zero {m : ℕ} {z : ℕ → F}
    (hz : ComplexityLE m z) (hinit : ∀ i : ℕ, i < m → z i = 0) : z = 0 := by
  obtain ⟨c, hc⟩ := hz
  set E : LinearRecurrence F := ⟨m, c⟩ with hE
  have hsol : E.IsSolution z := hc
  have hsol0 : E.IsSolution (0 : ℕ → F) := by intro n; simp
  refine (E.sol_eq_of_eq_init z 0 hsol hsol0).mpr ?_
  intro i hi
  simp only [Finset.coe_range, Set.mem_Iio] at hi
  exact hinit i hi


variable [Nontrivial F]

/-- Conversely, a stream of complexity at most `L` is annihilated by a monic
polynomial of degree `L`. -/
theorem exists_monic_annihilator {L : ℕ} {x : ℕ → F} (hx : ComplexityLE L x) :
    ∃ r : F[X], r.Monic ∧ r.natDegree = L ∧
      (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) r) x = 0 := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨(⟨L, c⟩ : LinearRecurrence F).charPoly,
    LinearRecurrence.charPoly_monic _, ?_, (isSolution_iff_aeval _ x).mp hc⟩
  exact Polynomial.natDegree_eq_of_degree_eq_some
    (LinearRecurrence.charPoly_degree_eq_order (E := (⟨L, c⟩ : LinearRecurrence F)))

variable [NoZeroDivisors F]

/-- **Linear complexity is subadditive.**  Annihilators multiply, so the sum of
a complexity-`L` stream and a complexity-`M` stream has complexity at most
`L + M`.  Mixing two PRNG streams therefore cannot hide them from a detector
that searches up to order `L + M`. -/
theorem complexityLE_add {L M : ℕ} {x y : ℕ → F} (hx : ComplexityLE L x)
    (hy : ComplexityLE M y) : ComplexityLE (L + M) (x + y) := by
  obtain ⟨p, hpm, hpd, hpx⟩ := exists_monic_annihilator hx
  obtain ⟨q, hqm, hqd, hqy⟩ := exists_monic_annihilator hy
  refine complexityLE_of_annihilated (hpm.mul hqm) ?_ ?_
  · rw [Polynomial.natDegree_mul hpm.ne_zero hqm.ne_zero, hpd, hqd]
  · have hx' : (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) (p * q)) x = 0 := by
      rw [mul_comm p q, map_mul, Module.End.mul_apply, hpx, map_zero]
    have hy' : (Polynomial.aeval (shift : (ℕ → F) →ₗ[F] (ℕ → F)) (p * q)) y = 0 := by
      rw [map_mul, Module.End.mul_apply, hqy, map_zero]
    rw [map_add, hx', hy', add_zero]

/-- Subadditivity for differences. -/
theorem complexityLE_sub {L M : ℕ} {x y : ℕ → F} (hx : ComplexityLE L x)
    (hy : ComplexityLE M y) : ComplexityLE (L + M) (x - y) := by
  have hneg : ComplexityLE M (-y) := by
    obtain ⟨d, hd⟩ := hy
    refine ⟨d, fun n => ?_⟩
    simp only [Pi.neg_apply, hd n, Finset.sum_neg_distrib, mul_neg]
  have := complexityLE_add hx hneg
  simpa [sub_eq_add_neg] using this



/-! ### Bridge to Mathlib's `LinearRecurrence` -/





open PRNGSeed in
theorem solution{L : ℕ} {x y : ℕ → F}
    (hx : ComplexityLE L x) (hy : ComplexityLE L y)
    (hagree : ∀ i : ℕ, i < 2 * L → x i = y i) : x = y := by
  have hdiff : ComplexityLE (L + L) (x - y) := complexityLE_sub hx hy
  have hzero : x - y = 0 := by
    refine eq_zero_of_complexityLE_of_init_zero hdiff ?_
    intro i hi
    have : i < 2 * L := by omega
    simp [hagree i this]
  have := sub_eq_zero.mp hzero
  exact this
