-- Prove2me | solution 1 for ProofsInTheBook.Chapter22Stable.derivative_roots_im_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:08:29.622091+00:00
-- url     : https://prove2.me/submissions/9b2301c9-2567-47c6-aca8-a589ef8094c5

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
open ProofsInTheBook.Chapter22Stable
open MvPolynomial
open Polynomial

lemma solution (p : Polynomial ℂ)
    (hp : ∀ z ∈ p.roots, z.im ≤ 0) :
    ∀ z ∈ (Polynomial.derivative p).roots, z.im ≤ 0 := by
  classical
  intro w hw
  by_contra hnot
  have hwpos : 0 < w.im := lt_of_not_ge hnot
  have hder_info := Polynomial.mem_roots'.mp hw
  have hder_ne : Polynomial.derivative p ≠ 0 := hder_info.1
  have hder_root : (Polynomial.derivative p).IsRoot w := hder_info.2
  have hder_eval : Polynomial.eval w (Polynomial.derivative p) = 0 := by
    simpa [Polynomial.IsRoot] using hder_root
  have hp_ne : p ≠ 0 := by
    intro hp0
    apply hder_ne
    rw [hp0, Polynomial.derivative_zero]
  by_cases hpw : Polynomial.eval w p = 0
  · have hmem : w ∈ p.roots :=
      Polynomial.mem_roots'.mpr ⟨hp_ne, by simpa [Polynomial.IsRoot] using hpw⟩
    have := hp w hmem
    linarith
  · have hsum_eq :
        (p.roots.map fun r => 1 / (w - r)).sum = 0 := by
      have hlog := (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpw
      rw [hder_eval, zero_div] at hlog
      simpa using hlog.symm
    have hdeg_pos : 0 < p.natDegree := by
      by_contra hdeg_not
      have hdeg0 : p.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg_not
      have hder0 : Polynomial.derivative p = 0 := Polynomial.derivative_of_natDegree_zero hdeg0
      exact hder_ne hder0
    have hroots_nonempty : p.roots ≠ 0 := by
      have hcard : p.roots.card = p.natDegree :=
        Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
      intro hzero
      have : p.natDegree = 0 := by
        rw [← hcard, hzero]
        simp
      omega
    have him_lt :
        ((p.roots.map fun r => 1 / (w - r)).sum).im < 0 := by
      have him_sum :
          ((p.roots.map fun r => 1 / (w - r)).sum).im =
            (p.roots.map fun r => (1 / (w - r)).im).sum := by
        simpa using
          (Complex.imAddGroupHom.map_multiset_sum
            (p.roots.map fun r => 1 / (w - r)))
      rw [him_sum]
      have hlt :
          (p.roots.map fun r => (1 / (w - r)).im).sum <
            (p.roots.map fun _r => (0 : ℝ)).sum := by
        apply Multiset.sum_lt_sum_of_nonempty hroots_nonempty
        intro r hr
        have hrim : r.im ≤ 0 := hp r hr
        have hsub_ne : w - r ≠ 0 := by
          intro hwr
          have hw_eq_r : w = r := sub_eq_zero.mp hwr
          linarith [hrim, hwpos, congrArg Complex.im hw_eq_r]
        have hnorm_pos : 0 < Complex.normSq (w - r) :=
          Complex.normSq_pos.mpr hsub_ne
        rw [one_div, Complex.inv_im]
        have hnum_pos : 0 < (w - r).im := by
          simp [Complex.sub_im]
          linarith
        have : - (w - r).im / Complex.normSq (w - r) < 0 :=
          div_neg_of_neg_of_pos (neg_neg_of_pos hnum_pos) hnorm_pos
        exact this
      simpa using hlt
    rw [hsum_eq] at him_lt
    simpa using him_lt
