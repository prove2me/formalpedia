-- Prove2me | solution 1 for ProofsInTheBook.Chapter22Gurvits.gurvits_product_telescopes
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:23.80991+00:00
-- url     : https://prove2.me/submissions/f472cf6a-3042-437d-b768-ab14e0b5f7bf

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

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∏ m ∈ Finset.Icc 2 n, G m = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 1 with hn1 | hn1
      · -- n = 0, so n+1 = 1: empty product, RHS = 1!/1 = 1
        interval_cases n
        simp
      · -- n ≥ 1: peel off the top factor G(n+1)
        rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1), ih hn1, G_succ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_pow]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
        ring
