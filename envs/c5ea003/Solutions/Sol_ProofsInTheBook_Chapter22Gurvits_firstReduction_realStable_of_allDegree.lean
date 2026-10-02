-- Prove2me | solution 1 for ProofsInTheBook.Chapter22Gurvits.firstReduction_realStable_of_allDegree
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:08:21.165288+00:00
-- url     : https://prove2.me/submissions/21679f07-0af0-4ad9-9f14-56b47d252f35

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







open Polynomial in
/-- **Half-plane Gauss-Lucas, univariate form.** If every root of a complex polynomial lies in
the closed lower half-plane, then every root of its derivative also lies in the closed lower
half-plane. -/
lemma derivative_roots_im_nonpos (p : Polynomial ℂ)
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





noncomputable section











lemma roots_im_nonpos_of_tendsto_eventually (d : ℕ) (q : ℕ → Polynomial ℂ)
    (qlim : Polynomial ℂ)
    (hdeg : ∀ᶠ n in Filter.atTop, (q n).natDegree = d)
    (hdeglim : qlim.natDegree = d) (hlim0 : qlim ≠ 0)
    (hcoeff : ∀ k, Filter.Tendsto (fun n => (q n).coeff k) Filter.atTop (nhds (qlim.coeff k)))
    (hroots : ∀ᶠ n in Filter.atTop, ∀ z ∈ (q n).roots, z.im ≤ 0) :
    ∀ z ∈ qlim.roots, z.im ≤ 0 := by
  classical
  obtain ⟨Ndeg, hNdeg⟩ := Filter.eventually_atTop.mp hdeg
  obtain ⟨Nroots, hNroots⟩ := Filter.eventually_atTop.mp hroots
  let N := max Ndeg Nroots
  let q' : ℕ → Polynomial ℂ := fun n => q (n + N)
  have hdeg' : ∀ n, (q' n).natDegree = d := by
    intro n
    exact hNdeg (n + N) (by dsimp [N]; omega)
  have hcoeff' : ∀ k, Filter.Tendsto (fun n => (q' n).coeff k)
      Filter.atTop (nhds (qlim.coeff k)) := by
    intro k
    exact (hcoeff k).comp (Filter.tendsto_add_atTop_nat N)
  have hroots' : ∀ n, ∀ z ∈ (q' n).roots, z.im ≤ 0 := by
    intro n
    exact hNroots (n + N) (by dsimp [N]; omega)
  exact roots_im_nonpos_of_tendsto d q' qlim hdeg' hdeglim hlim0 hcoeff' hroots'

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













































lemma coeff_firstReduction {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (a : Fin m →₀ ℕ) :
    MvPolynomial.coeff a (firstReduction p) =
      MvPolynomial.coeff (Finsupp.cons 1 a) p := by
  simpa [firstReduction] using MvPolynomial.finSuccEquiv_coeff_coeff a p 1

lemma firstReduction_nonnegativeCoefficients {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) :
    NonnegativeCoefficients (firstReduction p) := by
  intro a
  rw [coeff_firstReduction]
  exact hp _

lemma firstReduction_isHomogeneous {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : p.IsHomogeneous (m + 1)) :
    (firstReduction p).IsHomogeneous m := by
  simpa [firstReduction] using
    hp.finSuccEquiv_coeff_isHomogeneous 1 m (by omega)



lemma allDegreeCoefficientsPositive_firstReduction {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p) :
    AllDegreeCoefficientsPositive m (firstReduction p) := by
  intro a hdeg
  rw [coeff_firstReduction]
  have hcons : (Finsupp.cons 1 a).degree = m + 1 := by
    rw [degree_cons, hdeg]
    omega
  exact hp (Finsupp.cons 1 a) hcons



















lemma coeff_prod_of_natDegree_le_sum {ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (s : Finset ι) (f : ι → Polynomial R) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) =
      ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      have hprod : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, d j := by
        exact (Polynomial.natDegree_prod_le (s := s) (f := f)).trans
          (Finset.sum_le_sum fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert his, Finset.sum_insert his, Finset.prod_insert his]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (h i (Finset.mem_insert_self i s)) hprod]
      rw [ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

lemma coeff_linear_pow_top {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R) ^ n).coeff n = b ^ n := by
  have hlin : (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R).natDegree ≤ 1 := by
    simpa only [add_comm] using (Polynomial.natDegree_linear_le (a := b) (b := a))
  have h := Polynomial.coeff_pow_of_natDegree_le
    (p := (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R)) (m := n) (n := 1) hlin
  have hcoeff : (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R).coeff 1 = b := by
    simp
  rw [Nat.mul_one, hcoeff] at h
  exact h

lemma coeff_complexLineSection_monomial_degree {m : ℕ}
    (u : Fin m →₀ ℕ) (c : ℂ) (a b : Fin m → ℂ) :
    (complexLineSection (MvPolynomial.monomial u c) a b).coeff u.degree =
      c * ∏ i ∈ u.support, b i ^ u i := by
  classical
  rw [complexLineSection, MvPolynomial.eval₂_monomial, Polynomial.coeff_C_mul]
  have hprod :
      (∏ x ∈ u.support,
          (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff
        (∑ x ∈ u.support, u x) =
        ∏ x ∈ u.support,
          (((Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff (u x)) :=
    coeff_prod_of_natDegree_le_sum u.support
      (fun x => (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)
      (fun x => u x)
      (by
        intro x _hx
        have hlin :
            (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
          simpa only [add_comm] using
            (Polynomial.natDegree_linear_le (a := b x) (b := a x))
        simpa only [Nat.mul_one] using Polynomial.natDegree_pow_le_of_le (u x) hlin)
  rw [Finsupp.prod]
  change c *
      (∏ x ∈ u.support,
        (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff
        (∑ x ∈ u.support, u x) =
    c * ∏ i ∈ u.support, b i ^ u i
  rw [hprod]
  congr 1
  apply Finset.prod_congr rfl
  intro x _hx
  exact coeff_linear_pow_top (a x) (b x) (u x)

lemma complexLineSection_coeff_of_isHomogeneous {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) :
    (complexLineSection q a b).coeff d = MvPolynomial.eval b q := by
  classical
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro u hu
  have hdeg : u.degree = d := by
    rw [← hq (MvPolynomial.mem_support_iff.mp hu)]
    rw [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum]
    change (∑ i ∈ u.support, u i) =
      ∑ a ∈ u.support, u a • ((1 : Fin m → ℕ) a)
    simp
  rw [← hdeg]
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff u.degree =
      MvPolynomial.coeff u q * ∏ i ∈ u.support, b i ^ u i
  rw [coeff_complexLineSection_monomial_degree]

lemma complexLineSection_monomial_natDegree_le_degree {m : ℕ}
    (u : Fin m →₀ ℕ) (c : ℂ) (a b : Fin m → ℂ) :
    (complexLineSection (MvPolynomial.monomial u c) a b).natDegree ≤ u.degree := by
  classical
  rw [complexLineSection, MvPolynomial.eval₂_monomial]
  refine (Polynomial.natDegree_C_mul_le c _).trans ?_
  have hprod :
      (∏ x ∈ u.support,
          ((Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)).natDegree
        ≤ ∑ x ∈ u.support, u x := by
    exact (Polynomial.natDegree_prod_le
      (s := u.support)
      (f := fun x => (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)).trans
      (Finset.sum_le_sum fun x _hx => by
        have hlin :
            (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
          simpa only [add_comm] using
            (Polynomial.natDegree_linear_le (a := b x) (b := a x))
        simpa only [Nat.mul_one] using Polynomial.natDegree_pow_le_of_le (u x) hlin)
  rw [Finsupp.degree]
  exact hprod

lemma complexLineSection_natDegree_le_of_isHomogeneous {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) :
    (complexLineSection q a b).natDegree ≤ d := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  have hdeg : u.degree = d := by
    rw [← hq (MvPolynomial.mem_support_iff.mp hu)]
    rw [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum]
    change (∑ i ∈ u.support, u i) =
      ∑ a ∈ u.support, u a • ((1 : Fin m → ℕ) a)
    simp
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff N = 0
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (complexLineSection_monomial_natDegree_le_degree u (MvPolynomial.coeff u q) a b)
      (by omega))

lemma complexLineSection_natDegree_le_totalDegree {m : ℕ}
    (q : MvPolynomial (Fin m) ℂ) (a b : Fin m → ℂ) :
    (complexLineSection q a b).natDegree ≤ q.totalDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff N = 0
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (complexLineSection_monomial_natDegree_le_degree u (MvPolynomial.coeff u q) a b)
      (lt_of_le_of_lt (MvPolynomial.le_totalDegree hu) hN))

lemma complexLineSection_natDegree_eq_of_isHomogeneous_eval_ne_zero {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) (hbq : MvPolynomial.eval b q ≠ 0) :
    (complexLineSection q a b).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (complexLineSection_natDegree_le_of_isHomogeneous hq a b)
  rw [complexLineSection_coeff_of_isHomogeneous hq a b]
  exact hbq

lemma complexLineSection_firstReduction_natDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hhom : p.IsHomogeneous (m + 1))
    (hp_ne : firstReduction p ≠ 0)
    (a b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    (complexLineSection ((firstReduction p).map (algebraMap ℝ ℂ))
      (fun j => (a j : ℂ)) (fun j => (b j : ℂ))).natDegree = m := by
  have hhomC : ((firstReduction p).map (algebraMap ℝ ℂ)).IsHomogeneous m := by
    simpa using (firstReduction_isHomogeneous hhom).map (algebraMap ℝ ℂ)
  have hpos : 0 < MvPolynomial.eval b (firstReduction p) :=
    eval_pos_of_nonnegativeCoefficients (firstReduction_nonnegativeCoefficients hpcoeff) hp_ne hb
  have hmap_eval :
      MvPolynomial.eval (fun j => (b j : ℂ))
        ((firstReduction p).map (algebraMap ℝ ℂ)) =
        (MvPolynomial.eval b (firstReduction p) : ℂ) := by
    simpa [Function.comp_def] using
      (MvPolynomial.map_eval (q := algebraMap ℝ ℂ) (g := b) (p := firstReduction p)).symm
  apply complexLineSection_natDegree_eq_of_isHomogeneous_eval_ne_zero hhomC
  rw [hmap_eval]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)



lemma distinguishedDerivativeAt_zero {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) :
    distinguishedDerivativeAt p 0 = (firstReduction p).map (algebraMap ℝ ℂ) := by
  ext a
  simp only [distinguishedDerivativeAt, firstReduction, MvPolynomial.C_0]
  rw [Polynomial.eval, Polynomial.eval₂_at_zero]
  rw [Polynomial.coeff_derivative]
  simp
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map, MvPolynomial.coeff_map,
    MvPolynomial.finSuccEquiv_coeff_coeff]

lemma complexLineSection_coeff_eval_C_eq_sum {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (a b : Fin m → ℂ) (k : ℕ) (c : ℂ) :
    (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        c ^ i * (complexLineSection (P.coeff i) a b).coeff k := by
  rw [Polynomial.eval_eq_sum_range]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [MvPolynomial.eval₂_mul]
  have hCpow :
      MvPolynomial.eval₂ Polynomial.C
        (fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)
        (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ) = Polynomial.C (c ^ i) := by
    simp
  rw [hCpow, mul_comm, Polynomial.coeff_C_mul]
  rfl

lemma continuous_complexLineSection_coeff_eval_C {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (a b : Fin m → ℂ) (k : ℕ) :
    Continuous fun c : ℂ =>
      (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k := by
  rw [show (fun c : ℂ =>
        (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k) =
      fun c : ℂ => ∑ i ∈ Finset.range (P.natDegree + 1),
        c ^ i * (complexLineSection (P.coeff i) a b).coeff k by
    funext c
    exact complexLineSection_coeff_eval_C_eq_sum P a b k c]
  exact continuous_finsetSum _ (fun i _ => (continuous_id.pow i).mul continuous_const)

lemma derivative_finSuccEquiv_coeff_totalDegree_le {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hhom : p.IsHomogeneous (m + 1)) (i : ℕ) :
    (Polynomial.coeff
      (Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))) i).totalDegree ≤ m := by
  let Q := MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))
  change (Polynomial.coeff (Polynomial.derivative Q) i).totalDegree ≤ m
  rw [Polynomial.coeff_derivative]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hconst : ((↑i + 1 : MvPolynomial (Fin m) ℂ).totalDegree) = 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    rw [← MvPolynomial.C_eq_coe_nat (R := ℂ) (σ := Fin m) (i + 1)]
    rw [MvPolynomial.totalDegree_C]
  rw [hconst]
  change (Polynomial.coeff Q (i + 1)).totalDegree + 0 ≤ m
  by_cases hq : Polynomial.coeff Q (i + 1) = 0
  · rw [hq, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le m
  · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      (p.map (algebraMap ℝ ℂ)) (i + 1) hq
    change (Polynomial.coeff Q (i + 1)).totalDegree + (i + 1) ≤
      (p.map (algebraMap ℝ ℂ)).totalDegree at hle
    have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
      simpa using hhom.map (algebraMap ℝ ℂ)
    have htot : (p.map (algebraMap ℝ ℂ)).totalDegree ≤ m + 1 := hhomC.totalDegree_le
    omega

lemma distinguishedDerivativeAt_totalDegree_le {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hhom : p.IsHomogeneous (m + 1)) (c : ℂ) :
    (distinguishedDerivativeAt p c).totalDegree ≤ m := by
  rw [distinguishedDerivativeAt, Polynomial.eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _hi
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hCpow_le : (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ).totalDegree ≤ 0 := by
    simpa [MvPolynomial.totalDegree_C] using
      (MvPolynomial.totalDegree_pow (MvPolynomial.C c : MvPolynomial (Fin m) ℂ) i)
  have hCpow : (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ).totalDegree = 0 :=
    le_antisymm hCpow_le (Nat.zero_le _)
  rw [hCpow]
  simpa using derivative_finSuccEquiv_coeff_totalDegree_le hhom i





lemma complexLineSection_eval {m : ℕ} (q : MvPolynomial (Fin m) ℂ)
    (a b : Fin m → ℂ) (t : ℂ) :
    Polynomial.eval t (complexLineSection q a b) =
      MvPolynomial.eval (fun j => a j + b j * t) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial u c =>
      rw [complexLineSection, MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial,
        Polynomial.eval_mul, Polynomial.eval_C]
      congr 1
      rw [Finsupp.prod, Polynomial.eval_prod, Finsupp.prod]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
  | add p q hp hq =>
      rw [complexLineSection, MvPolynomial.eval₂_add, Polynomial.eval_add,
        MvPolynomial.eval_add]
      change Polynomial.eval t (complexLineSection p a b) +
          Polynomial.eval t (complexLineSection q a b) =
        (MvPolynomial.eval (fun j => a j + b j * t) p) +
          (MvPolynomial.eval (fun j => a j + b j * t) q)
      rw [hp, hq]

lemma distinguishedDerivativeAt_eval {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (z : Fin m → ℂ) (c : ℂ) :
    MvPolynomial.eval z (distinguishedDerivativeAt p c) =
      Polynomial.eval c (Polynomial.derivative (complexSectionPolynomial p z)) := by
  let P := Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))
  have h :
      Polynomial.eval₂ (MvPolynomial.eval z) c P =
        MvPolynomial.eval z (Polynomial.eval (MvPolynomial.C c) P) := by
    simpa using
      (Polynomial.eval₂_hom (p := P) (f := MvPolynomial.eval z) (x := MvPolynomial.C c))
  simp [distinguishedDerivativeAt, complexSectionPolynomial, Polynomial.derivative_map,
    Polynomial.eval_map, P, h.symm]



lemma distinguishedDerivativeLine_eval_ne_zero_of_section_derivative_ne_zero {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : ProofsInTheBook.Chapter22Stable.RealStable p)
    {c : ℂ} (hc : 0 < c.im) (a b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    ∀ t : ℂ, 0 < t.im →
      Polynomial.derivative
          (complexSectionPolynomial p (fun j => (a j : ℂ) + (b j : ℂ) * t)) ≠ 0 →
      Polynomial.eval t
          (complexLineSection (distinguishedDerivativeAt p c)
            (fun j => (a j : ℂ)) (fun j => (b j : ℂ))) ≠ 0 := by
  intro t ht hder_ne hzero
  let z : Fin m → ℂ := fun j => (a j : ℂ) + (b j : ℂ) * t
  have hz : ∀ j, 0 < (z j).im := by
    intro j
    dsimp [z]
    simp [Complex.mul_im]
    exact mul_pos (hb j) ht
  have hsection_no_roots :
      ∀ w : ℂ, 0 < w.im → Polynomial.eval w (complexSectionPolynomial p z) ≠ 0 :=
    complexSectionPolynomial_no_uhp_root hp hz
  have hsection_roots :
      ∀ w ∈ (complexSectionPolynomial p z).roots, w.im ≤ 0 := by
    intro w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    exact hsection_no_roots w hwpos (by simpa [Polynomial.IsRoot] using hroot)
  have hder_roots :
      ∀ w ∈ (Polynomial.derivative (complexSectionPolynomial p z)).roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.derivative_roots_im_nonpos
      (complexSectionPolynomial p z) hsection_roots
  have hczero :
      Polynomial.eval c (Polynomial.derivative (complexSectionPolynomial p z)) = 0 := by
    have hline :=
      complexLineSection_eval (distinguishedDerivativeAt p c)
        (fun j => (a j : ℂ)) (fun j => (b j : ℂ)) t
    rw [hline] at hzero
    have hdist := distinguishedDerivativeAt_eval p z c
    simpa [z] using hdist.symm.trans hzero
  have hcmem : c ∈ (Polynomial.derivative (complexSectionPolynomial p z)).roots :=
    Polynomial.mem_roots'.mpr ⟨hder_ne, by simpa [Polynomial.IsRoot] using hczero⟩
  have := hder_roots c hcmem
  linarith























































lemma tendsto_I_inv_nat :
    Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hepsR : Filter.Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)⁻¹ : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
      Filter.atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsR
  simpa using hepsC.mul tendsto_const_nhds

lemma I_inv_nat_im_pos (N : ℕ) :
    0 < ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I).im := by
  simp only [Complex.mul_I_im]
  rw [Complex.inv_re]
  have hpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hnorm : 0 < Complex.normSq ((((N + 1 : ℕ) : ℝ) : ℂ)) := by
    exact Complex.normSq_pos.mpr (by exact_mod_cast ne_of_gt hpos)
  exact div_pos hpos hnorm

lemma firstReduction_ne_zero_of_allDegree {m : ℕ} (hm : 1 ≤ m)
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p) :
    firstReduction p ≠ 0 := by
  let j0 : Fin m := ⟨0, by omega⟩
  let a : Fin m →₀ ℕ := Finsupp.single j0 m
  have hpos : 0 < MvPolynomial.coeff a (firstReduction p) :=
    allDegreeCoefficientsPositive_firstReduction hp a (by simp [a])
  intro hzero
  rw [hzero] at hpos
  simp at hpos

lemma complexSectionPolynomial_derivative_ne_zero_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1)) (z : Fin m → ℂ) :
    Polynomial.derivative (complexSectionPolynomial p z) ≠ 0 := by
  intro hder
  have hnat0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder
  have hnat := complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom z
  rw [hnat] at hnat0
  omega

























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

lemma solution {m : ℕ} (hm : 1 ≤ m)
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p) :
    ProofsInTheBook.Chapter22Stable.RealStable (firstReduction p) := by
  intro z hz hzero
  let ar : Fin m → ℝ := fun j => (z j).re
  let br : Fin m → ℝ := fun j => (z j).im
  let a : Fin m → ℂ := fun j => (ar j : ℂ)
  let b : Fin m → ℂ := fun j => (br j : ℂ)
  let cN : ℕ → ℂ := fun N => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I)
  let qN : ℕ → Polynomial ℂ := fun N =>
    complexLineSection (distinguishedDerivativeAt p (cN N)) a b
  let q0 : Polynomial ℂ :=
    complexLineSection ((firstReduction p).map (algebraMap ℝ ℂ)) a b
  have hbpos : ∀ j, 0 < br j := by
    intro j
    exact hz j
  have hfr_ne : firstReduction p ≠ 0 := firstReduction_ne_zero_of_allDegree hm hp
  have hdeg0 : q0.natDegree = m := by
    dsimp [q0, a, b]
    exact complexLineSection_firstReduction_natDegree hpcoeff hhom hfr_ne ar br hbpos
  have hq0_ne : q0 ≠ 0 := by
    intro hq
    have := hdeg0
    rw [hq, Polynomial.natDegree_zero] at this
    omega
  have hq0_coeff_m_ne : q0.coeff m ≠ 0 := by
    have hlead := Polynomial.leadingCoeff_ne_zero.mpr hq0_ne
    simpa [Polynomial.leadingCoeff, hdeg0] using hlead
  have hcoeff : ∀ k, Filter.Tendsto (fun N : ℕ => (qN N).coeff k) Filter.atTop
      (nhds (q0.coeff k)) := by
    intro k
    let P : Polynomial (MvPolynomial (Fin m) ℂ) :=
      Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))
    have ht := (continuous_complexLineSection_coeff_eval_C P a b k).tendsto 0
    have ht' := ht.comp tendsto_I_inv_nat
    have hlimit :
        complexLineSection (Polynomial.eval (MvPolynomial.C 0) P) a b = q0 := by
      dsimp [P, q0]
      simpa [distinguishedDerivativeAt] using
        congrArg (fun q => complexLineSection q a b) (distinguishedDerivativeAt_zero p)
    rw [hlimit] at ht'
    simpa [Function.comp_def, qN, cN, P, distinguishedDerivativeAt] using ht'
  have hdegN_eventually : ∀ᶠ N in Filter.atTop, (qN N).natDegree = m := by
    have hnorm_tend := (hcoeff m).norm
    have hnorm_pos : 0 < ‖q0.coeff m‖ := norm_pos_iff.mpr hq0_coeff_m_ne
    have hev : ∀ᶠ N in Filter.atTop, 0 < ‖(qN N).coeff m‖ :=
      hnorm_tend.eventually (lt_mem_nhds hnorm_pos)
    filter_upwards [hev] with N hNnorm
    have hcoeff_ne : (qN N).coeff m ≠ 0 := norm_pos_iff.mp hNnorm
    have hle : (qN N).natDegree ≤ m := by
      dsimp [qN]
      exact (complexLineSection_natDegree_le_totalDegree (distinguishedDerivativeAt p (cN N)) a b).trans
        (distinguishedDerivativeAt_totalDegree_le hhom (cN N))
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff_ne
  have hrootsN : ∀ᶠ N in Filter.atTop, ∀ w ∈ (qN N).roots, w.im ≤ 0 := by
    apply Filter.Eventually.of_forall
    intro N w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    have hne_der : Polynomial.derivative
        (complexSectionPolynomial p (fun j => (ar j : ℂ) + (br j : ℂ) * w)) ≠ 0 :=
      complexSectionPolynomial_derivative_ne_zero_of_allDegree hp hhom _
    have hne := distinguishedDerivativeLine_eval_ne_zero_of_section_derivative_ne_zero hstable
      (I_inv_nat_im_pos N) ar br hbpos w hwpos hne_der
    exact hne (by simpa [qN, cN, a, b, Polynomial.IsRoot] using hroot)
  have hroots0 : ∀ w ∈ q0.roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.roots_im_nonpos_of_tendsto_eventually m qN q0
      hdegN_eventually hdeg0 hq0_ne hcoeff hrootsN
  have hz_repr : (fun j : Fin m => (ar j : ℂ) + (br j : ℂ) * Complex.I) = z := by
    funext j
    apply Complex.ext <;> simp [ar, br]
  have hIroot_eval : Polynomial.eval Complex.I q0 = 0 := by
    dsimp [q0, a, b]
    rw [complexLineSection_eval, hz_repr]
    simpa using hzero
  have hImem : Complex.I ∈ q0.roots :=
    Polynomial.mem_roots'.mpr ⟨hq0_ne, by simpa [Polynomial.IsRoot] using hIroot_eval⟩
  have hI_im_nonpos := hroots0 Complex.I hImem
  norm_num at hI_im_nonpos
