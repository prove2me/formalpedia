-- Prove2me | solution 1 for ProofsInTheBook.Chapter22Gurvits.univariate_gurvits_factored
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:27.770068+00:00
-- url     : https://prove2.me/submissions/6e427634-657a-4036-a715-5c14b29c86b6

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PermanentConvexity -/
section
set_option autoImplicit true


/-!
# Permanent convexity lemmas

This file is independent of `Chapter22`.  It records algebraic permanent
facts used in Van der Waerden-style arguments:

* additivity and affine-linearity in one row or one column;
* bilinearity of the permanent after two rows are singled out;
* the quadratic expansion along a two-row line, and the resulting convexity
  criterion when the mixed quadratic coefficient is nonnegative;
* the discharge of that mixed-coefficient hypothesis for the elementary
  `2 × 2` checkerboard exchange directions;
* the maximal feasible checkerboard exchange step, which keeps the
  doubly-stochastic constraints and forces a boundary zero;
* the elementary `2 × 2` row log-concavity model.

The deep Alexandrov-Fenchel/Falikman-Egorychev/Gurvits log-concavity input is
not hidden here.  The general convexity theorem below states exactly the local
mixed-coefficient nonnegativity hypothesis needed for a two-row slice.
-/

namespace ProofsInTheBook.PermanentConvexity

open Matrix

noncomputable section

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ## Basic multilinearity -/

variable {R : Type*} [CommSemiring R]











/-! ## Two-row slices -/



















/-! ## Doubly-stochastic two-row perturbations -/











/-! ## Checkerboard exchange directions -/

































/-! ## Quadratic expansion and convexity along a two-row line -/

variable {M : Matrix n n ℝ} {r s : n}











































/-! ## Elementary `2 × 2` log-concavity model -/







end

end ProofsInTheBook.PermanentConvexity

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PermanentConvexity
-/
/- Source module: ProofsInTheBook.Chapter22 -/
section
set_option autoImplicit true


/-!
# Chapter 22: Van der Waerden's permanent conjecture

From "Proofs from THE BOOK":

**Van der Waerden's conjecture** (now theorem, proved by Falikman and
Egorychev): The permanent of a doubly stochastic n×n matrix is minimized
by the matrix with all entries 1/n, giving perm ≥ n!/nⁿ.

The book presents the proof using the theory of mixed discriminants.

Formalization status: this file now states the genuine theorem over Mathlib's
`doublyStochastic` predicate.  The proved local part is the equality-case
computation for the flat matrix, the `n ≤ 2` unconditional lower bounds, the
`n = 0,1,2` instances of the coefficient-from-capacity analytic core, and the
weighted-AM-GM capacity lower bound for row-linear products of doubly
stochastic matrices.  It identifies the squarefree coefficient of the
row-linear `MvPolynomial` with the row-linear mixed coefficient and hence with
the permanent, and packages the checkerboard boundary-convexity step for
opposite exchange endpoints.  The remaining arbitrary-dimension lower bound is
exposed as a point-17 honest frontier: it is conditional on the missing
Falikman-Egorychev/Gurvits coefficient-from-capacity inequality for `n ≥ 3`,
now stated on the actual squarefree coefficient of the row-linear polynomial
rather than replaced by the flat-matrix special case.  The equality-only-if-flat
strengthening belongs to the same unformalized analytic equality-case layer.

The exact intended unconditional Lean endpoint is:

```
theorem van_der_waerden_permanent_conjecture (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent
```
-/

namespace ProofsInTheBook.Chapter22

open Matrix
open ProofsInTheBook.PermanentConvexity

noncomputable section

/-!
### The equality case and the honest analytic frontier

The van der Waerden theorem says every doubly stochastic matrix has permanent
at least `n! / n^n`, with equality at the flat matrix.
-/

































































/-!
### Elementary low-dimensional cases

The full theorem is deep, but dimensions `0`, `1`, and `2` are elementary.
These results discharge the analytic-core assumption in the small cases instead
of hiding them behind the frontier theorem.
-/



























/-! ### Boundary-convexity interface from checkerboard exchanges -/



















end

end ProofsInTheBook.Chapter22

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.Chapter22
-/
/- Source module: ProofsInTheBook.Chapter22Stable -/
section
set_option autoImplicit true


/-!
# Real-stable polynomials (toward Chapter 22, Gurvits capacity)

A real multivariate polynomial is **real-stable** if it has no zero with all variables in the
open upper half-plane. This is the polynomial class underlying Gurvits's capacity proof. Here we
build the definition and the closure properties that are elementary (product closure, stability of
nonnegative linear forms — hence of the row-linear product `∏ rows`). The hard remaining closure
(`∂/∂xₘ` preserves real-stability — the Lieb–Sokal lemma) is isolated as `DerivPreservesStable`.
-/

namespace ProofsInTheBook.Chapter22Stable

open MvPolynomial











/-!
### Univariate real-rootedness and its derivative closure (the univariate Lieb–Sokal heart)

A univariate real polynomial is real-rooted iff it splits over ℝ — equivalently its root multiset
(with multiplicity) has cardinality equal to its degree. The derivative of a real-rooted polynomial
is again real-rooted (Rolle's theorem / interlacing). This is the one-variable case of the stability
closure; the full multivariate Lieb–Sokal lemma (`∂/∂xₘ` preserves real-stability) lifts it via the
Hurwitz theorem and remains the genuine remaining analytic input for the Gurvits reduction.
-/













noncomputable section













end

end ProofsInTheBook.Chapter22Stable

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.Chapter22
import ProofsInTheBook.Chapter22Stable
-/
/- Source module: ProofsInTheBook.Chapter22Gurvits -/
section
set_option autoImplicit true


/-!
# Chapter 22 (van der Waerden permanent bound) — Gurvits capacity, algebraic core

The Gurvits capacity proof reduces `perm(A) ≥ n!/nⁿ` (for doubly stochastic `A`) to a chain of
capacity inequalities with reduction constant `G(k) = ((k-1)/k)^{k-1}`. The product of these
constants telescopes to exactly `n!/nⁿ` — that is the algebraic heart proved here. Blueprint:
`HANDOFF/CH22_GURVITS_CAPACITY.md`.
-/

namespace ProofsInTheBook.Chapter22Gurvits

open scoped BigOperators
open ProofsInTheBook.Chapter22

noncomputable section







/-- For `m ≥ 1`, `G(m+1) = (m/(m+1))^m`. -/
lemma G_succ (m : ℕ) : G (m + 1) = ((m : ℝ) / (m + 1 : ℝ)) ^ m := by
  simp only [G, Nat.add_sub_cancel]
  norm_num



/-!
### The AM-GM product bound (key inequality of the univariate Gurvits step)

For nonnegative `λ` and `t`, `∏ᵢ (1 + λᵢ t) ≤ (1 + (Σλ) t / k)^k`. This is AM-GM applied to the
`k` factors `1 + λᵢ t`, and it is the inequality that, evaluated at the optimal `t`, yields the
Gurvits capacity-reduction constant `G(k) = ((k-1)/k)^{k-1}`.
-/

/-- AM-GM: `∏ᵢ (1 + λᵢ t) ≤ (1 + (Σλ) t / k)^k` for nonnegative `λ`, `t`. -/
lemma prod_one_add_mul_le {k : ℕ} (hk : 1 ≤ k) (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) (ht : 0 ≤ t) :
    ∏ i, (1 + lam i * t) ≤ (1 + (∑ i, lam i) * t / k) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set y : Fin k → ℝ := fun i => 1 + lam i * t with hy_def
  have hy : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ y i := by
    intro i _; have : 0 ≤ lam i * t := mul_nonneg (hlam i) ht; simp only [hy_def]; linarith
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ ((k : ℝ)⁻¹) := by
    intro i _; positivity
  have hw' : ∑ _i : Fin k, ((k : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgeom := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (k : ℝ)⁻¹) y hw hw' hy
  -- ∏ y_i ^ (1/k) ≤ ∑ (1/k) y_i = avg
  set avg : ℝ := 1 + (∑ i, lam i) * t / k with havg_def
  have hsum : ∑ i, ((k : ℝ)⁻¹) * y i = avg := by
    rw [← Finset.mul_sum]
    have hsy : ∑ i, y i = (k : ℝ) + (∑ i, lam i) * t := by
      simp only [hy_def]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.sum_mul]
    rw [hsy, havg_def]
    field_simp
  rw [hsum] at hgeom
  -- ∏ y_i ^ (1/k) = (∏ y_i) ^ (1/k)
  have hprod_rpow : ∏ i, (y i) ^ ((k : ℝ)⁻¹) = (∏ i, y i) ^ ((k : ℝ)⁻¹) :=
    Real.finsetProd_rpow Finset.univ y hy _
  rw [hprod_rpow] at hgeom
  have hprodpos : 0 ≤ ∏ i, y i := Finset.prod_nonneg hy
  -- raise both sides to the (k:ℝ) power, then simplify the LHS exponent (1/k)*k = 1
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprodpos _) hgeom (le_of_lt hkR)
  rw [← Real.rpow_mul hprodpos] at hpow
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  rw [inv_mul_cancel₀ hkne, Real.rpow_one, Real.rpow_natCast] at hpow
  simpa [hy_def, havg_def] using hpow

/-- Power cancellation: `G(k) · (k/(k-1))^k = k/(k-1)` for `k ≥ 2`. -/
lemma G_mul_ratio_pow {k : ℕ} (hk : 2 ≤ k) :
    G k * ((k : ℝ) / ((k : ℝ) - 1)) ^ k = (k : ℝ) / ((k : ℝ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [G_succ]
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hkey : ((m : ℝ) / ((m : ℝ) + 1)) * (((m : ℝ) + 1) / (m : ℝ)) = 1 := by
    field_simp
  have hsimp : ((m : ℝ) + 1) / ((m : ℝ) + 1 - 1) = ((m : ℝ) + 1) / (m : ℝ) := by ring_nf
  rw [hsimp, pow_succ, ← mul_assoc, ← mul_pow, hkey, one_pow, one_mul]





/-!
### Capacity lower-bound bookkeeping for the reduction chain

The analytic-free stable-polynomial step is most convenient to state as a
lower-bound invariant rather than as an actual infimum.  `CapLB p c` means that
`c` is a certified lower bound for the Gurvits capacity of `p`.
-/









































































































































































































/-!
### Algebraic interface to the Chapter 22 capacity core

The analytic Gurvits step should produce the lower bound with the telescoping
product of the constants `G(2), ..., G(n)`.  The theorem below is the purely
algebraic last mile: once that iterated capacity estimate is available for the
row-linear polynomial, the exact `n! / n^n` squarefree-coefficient core follows.
-/





















end

end ProofsInTheBook.Chapter22Gurvits

end


set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

lemma solution {k : ℕ} (hk : 2 ≤ k) (c C : ℝ) (lam : Fin k → ℝ)
    (hc : 0 ≤ c) (hlam : ∀ i, 0 ≤ lam i) (hS : 0 < ∑ i, lam i)
    (hbound : ∀ t : ℝ, 0 < t → C * t ≤ c * ∏ i, (1 + lam i * t)) :
    G k * C ≤ c * ∑ i, lam i := by
  set S : ℝ := ∑ i, lam i with hSdef
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  set t0 : ℝ := (k : ℝ) / (S * ((k : ℝ) - 1)) with ht0def
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  have h3 : 1 + S * t0 / k = (k : ℝ) / ((k : ℝ) - 1) := by
    rw [ht0def]; field_simp; ring
  have h1 := hbound t0 ht0
  have h2 := prod_one_add_mul_le (by omega : 1 ≤ k) lam hlam t0 (le_of_lt ht0)
  have h4 : C * t0 ≤ c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k := by
    calc C * t0 ≤ c * ∏ i, (1 + lam i * t0) := h1
      _ ≤ c * (1 + S * t0 / k) ^ k := by
          apply mul_le_mul_of_nonneg_left _ hc; rw [hSdef]; exact h2
      _ = c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k := by rw [h3]
  -- multiply by G k ≥ 0, use the cancellation, and that c*k/(k-1) = c*S*t0
  have hGnn : 0 ≤ G k := by
    rw [G]; positivity
  have h5 : G k * (C * t0) ≤ G k * (c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k) :=
    mul_le_mul_of_nonneg_left h4 hGnn
  rw [show G k * (c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k)
        = c * (G k * ((k : ℝ) / ((k : ℝ) - 1)) ^ k) by ring, G_mul_ratio_pow hk] at h5
  -- h5 : G k * (C * t0) ≤ c * (k/(k-1)); and c*(k/(k-1)) = (c*S)*t0
  have h6 : c * ((k : ℝ) / ((k : ℝ) - 1)) = (c * S) * t0 := by
    rw [ht0def]; field_simp
  rw [h6, ← mul_assoc] at h5
  -- h5 : G k * C * t0 ≤ c * S * t0; cancel t0 > 0
  exact le_of_mul_le_mul_right h5 ht0
