-- Prove2me | solution 1 for ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:18.417397+00:00
-- url     : https://prove2.me/submissions/b2399c62-4cd3-456c-baa3-3ffdb9c5bd06

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



theorem flatDoublyStochasticMatrix_mem_doublyStochastic (n : ℕ) :
    flatDoublyStochasticMatrix n ∈ doublyStochastic ℝ (Fin n) := by
  classical
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · intro i
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt).ne'
    simp [flatDoublyStochasticMatrix, Finset.sum_const, Fintype.card_fin, hn]
  · intro j
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt).ne'
    simp [flatDoublyStochasticMatrix, Finset.sum_const, Fintype.card_fin, hn]









theorem eval_rowLinearMvPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (rowLinearMvPolynomial A) = rowLinearProduct A x := by
  simp [rowLinearMvPolynomial, rowLinearProduct]







private def permInvEquiv (α : Type*) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

/-- The mixed coefficient of the row-linear product is the permanent. -/
theorem rowLinearMixedCoefficient_eq_permanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearMixedCoefficient A = A.permanent := by
  classical
  unfold rowLinearMixedCoefficient Matrix.permanent
  refine (Fintype.sum_equiv (permInvEquiv (Fin n))
    (fun σ : Equiv.Perm (Fin n) => ∏ i, A i (σ i))
    (fun σ : Equiv.Perm (Fin n) => ∏ i, A (σ i) i) ?_).trans ?_
  · intro σ
    simp
    exact Fintype.prod_equiv σ
      (fun i => A i (σ i))
      (fun i => A (σ.symm i) i)
      (by intro i; simp)
  · rfl

private theorem sum_single_one_eq_squarefreeExponent_iff_bijective {n : ℕ}
    (f : Fin n → Fin n) :
    (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n ↔ Function.Bijective f := by
  constructor
  · intro h
    have hcard : ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).card = 1 := by
      intro j
      have hj : (∑ i, Finsupp.single (f i) 1) j = 1 := by
        rw [h]
        simp [squarefreeExponent]
      have hsum : (∑ i, (if f i = j then (1 : ℕ) else 0)) = 1 := by
        simpa [Finsupp.single_apply, eq_comm] using hj
      rw [Finset.card_eq_sum_ones]
      simpa [Finset.sum_filter] using hsum
    refine ⟨?_, ?_⟩
    · intro i k hik
      have hi : i ∈ Finset.univ.filter (fun x => f x = f i) := by simp
      have hk : k ∈ Finset.univ.filter (fun x => f x = f i) := by simp [hik]
      rcases Finset.card_eq_one.mp (hcard (f i)) with ⟨a, ha⟩
      have hi_eq : i = a := by simpa [ha] using hi
      have hk_eq : k = a := by simpa [ha] using hk
      exact hi_eq.trans hk_eq.symm
    · intro j
      rcases Finset.card_eq_one.mp (hcard j) with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have : i ∈ Finset.univ.filter (fun x => f x = j) := by simp [hi]
      simpa using this
  · intro hbij
    ext j
    have hsum : (∑ i, (if f i = j then (1 : ℕ) else 0)) = 1 := by
      rcases hbij.2 j with ⟨i, hi⟩
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro k _hk hki
        have hfk : f k ≠ j := by
          intro hkj
          exact hki (hbij.1 (hkj.trans hi.symm))
        simp [hfk]
      · intro hi_not
        exact (hi_not (Finset.mem_univ i)).elim
    have hleft : (∑ i, Finsupp.single (f i) 1) j =
        ∑ i, (if f i = j then (1 : ℕ) else 0) := by
      simp [Finsupp.single_apply, eq_comm]
    rw [hleft, hsum]
    simp [squarefreeExponent]

private theorem rowLinearTerm_eq_monomial {n : Type*} [DecidableEq n] [Fintype n]
    (a : n → ℝ) (f : n → n) :
    (∏ i, MvPolynomial.C (a i) * MvPolynomial.X (f i) : MvPolynomial n ℝ) =
      MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (∏ i, a i) := by
  classical
  simp_rw [show ∀ i, MvPolynomial.C (a i) * MvPolynomial.X (f i) =
      (MvPolynomial.monomial (Finsupp.single (f i) 1) (a i) : MvPolynomial n ℝ) by
    intro i
    rw [MvPolynomial.X, MvPolynomial.C_mul_monomial]
    simp]
  induction (Finset.univ : Finset n) using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      simp [Finset.prod_insert, Finset.sum_insert, his, ih, MvPolynomial.monomial_mul]

private theorem rowLinearMvPolynomial_expand {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearMvPolynomial A =
      ∑ f : Fin n → Fin n, ∏ i, MvPolynomial.C (A i (f i)) * MvPolynomial.X (f i) := by
  classical
  unfold rowLinearMvPolynomial
  rw [Fintype.prod_sum]

theorem rowLinearSquarefreeCoefficient_eq_function_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A =
      ∑ f : Fin n → Fin n, if Function.Bijective f then ∏ i, A i (f i) else 0 := by
  classical
  unfold rowLinearSquarefreeCoefficient
  rw [rowLinearMvPolynomial_expand A]
  simp_rw [rowLinearTerm_eq_monomial]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro f _hf
  have hcoeff : MvPolynomial.coeff (squarefreeExponent n)
      (MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (∏ i, A i (f i)) :
        MvPolynomial (Fin n) ℝ) =
      if (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n then
        ∏ i, A i (f i) else 0 := by
    rw [MvPolynomial.coeff_monomial]
  rw [hcoeff]
  by_cases hbij : Function.Bijective f
  · have hexp : (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n :=
      (sum_single_one_eq_squarefreeExponent_iff_bijective f).2 hbij
    rw [if_pos hexp, if_pos hbij]
  · have hexp : (∑ i, Finsupp.single (f i) 1) ≠ squarefreeExponent n := by
      intro h
      exact hbij ((sum_single_one_eq_squarefreeExponent_iff_bijective f).1 h)
    rw [if_neg hexp, if_neg hbij]

private def bijectiveFunctionEquivPerm (n : ℕ) :
    {f : Fin n → Fin n // Function.Bijective f} ≃ Equiv.Perm (Fin n) where
  toFun f := Equiv.ofBijective f.1 f.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact Equiv.ofBijective_apply f.1 f.2 i
  right_inv σ := by
    ext i
    rfl

private theorem function_sum_bijective_eq_rowLinearMixedCoefficient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin n → Fin n, if Function.Bijective f then ∏ i, A i (f i) else 0) =
      rowLinearMixedCoefficient A := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (s := Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f))]
  · unfold rowLinearMixedCoefficient
    exact Fintype.sum_equiv (bijectiveFunctionEquivPerm n)
      (fun f : {f : Fin n → Fin n // Function.Bijective f} => ∏ i, A i (f.1 i))
      (fun σ : Equiv.Perm (Fin n) => ∏ i, A i (σ i))
      (by intro f; rfl)
  · intro f
    simp

/-- The squarefree `MvPolynomial` coefficient is the row-linear mixed coefficient. -/
theorem rowLinearSquarefreeCoefficient_eq_mixedCoefficient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A = rowLinearMixedCoefficient A := by
  rw [rowLinearSquarefreeCoefficient_eq_function_sum,
    function_sum_bijective_eq_rowLinearMixedCoefficient]

/-- The squarefree `MvPolynomial` coefficient of the row-linear product is the permanent. -/
theorem rowLinearSquarefreeCoefficient_eq_permanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A = A.permanent := by
  rw [rowLinearSquarefreeCoefficient_eq_mixedCoefficient, rowLinearMixedCoefficient_eq_permanent]



/--
The weighted-AM-GM/capacity step in Gurvits's proof, specialized to the
row-linear product associated to a doubly stochastic matrix.
-/
theorem rowLinearCapacityAtLeastOne_of_doublyStochastic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    RowLinearCapacityAtLeastOne A := by
  classical
  refine ⟨?_⟩
  intro x hx
  have hfactor :
      ∀ i : Fin n, (∏ j, x j ^ A i j) ≤ ∑ j, A i j * x j := by
    intro i
    simpa using Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (w := fun j => A i j) (z := x)
      (fun j _ => nonneg_of_mem_doublyStochastic hA)
      (by simpa using sum_row_of_mem_doublyStochastic hA i)
      (fun j _ => le_of_lt (hx j))
  have hprod :
      (∏ i, ∏ j, x j ^ A i j) ≤ rowLinearProduct A x := by
    unfold rowLinearProduct
    exact Finset.prod_le_prod
      (fun _i _hi => Finset.prod_nonneg fun j _hj => Real.rpow_nonneg (le_of_lt (hx j)) _)
      (fun i _hi => hfactor i)
  calc
    (∏ j, x j) = ∏ j, x j ^ (1 : ℝ) := by
      simp [Real.rpow_one]
    _ = ∏ j, x j ^ (∑ i, A i j) := by
      simp [sum_col_of_mem_doublyStochastic hA]
    _ = ∏ j, ∏ i, x j ^ A i j := by
      refine Finset.prod_congr rfl ?_
      intro j _hj
      rw [Real.rpow_sum_of_pos (hx j)]
    _ = ∏ i, ∏ j, x j ^ A i j := by
      rw [Finset.prod_comm]
    _ ≤ rowLinearProduct A x := hprod





















/-!
### Elementary low-dimensional cases

The full theorem is deep, but dimensions `0`, `1`, and `2` are elementary.
These results discharge the analytic-core assumption in the small cases instead
of hiding them behind the frontier theorem.
-/

theorem van_der_Waerden_permanent_fin_zero
    (A : Matrix (Fin 0) (Fin 0) ℝ)
    (_hA : A ∈ doublyStochastic ℝ (Fin 0)) :
    ((0 : ℕ).factorial : ℝ) / (0 : ℝ) ^ 0 ≤ A.permanent := by
  simp [Matrix.permanent]

























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





/-- A nonempty finite product of real-stable polynomials is real-stable. -/
lemma RealStable.prod {m : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial (Fin m) ℝ} (hf : ∀ i ∈ s, RealStable (f i)) :
    RealStable (∏ i ∈ s, f i) := by
  intro z hz
  rw [map_prod, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => hf i hi z hz)

/-- A nonnegative linear form `∑ⱼ Cⱼ Xⱼ` with positive total weight is real-stable: its value at
any upper-half-plane point has strictly positive imaginary part. -/
lemma linearForm_stable {m : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hpos : 0 < ∑ j, C j) :
    RealStable (∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)) := by
  intro z hz
  have hval : MvPolynomial.eval z
      ((∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)).map (algebraMap ℝ ℂ))
      = ∑ j, (C j : ℂ) * z j := by
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, eval_C, eval_X]
    simp
  rw [hval]
  have him : (∑ j, (C j : ℂ) * z j).im = ∑ j, C j * (z j).im := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_im]
  have hExists : ∃ j, 0 < C j := by
    by_contra h
    push_neg at h
    have : ∑ j, C j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    linarith
  obtain ⟨j0, hj0⟩ := hExists
  have hpos' : 0 < (∑ j, (C j : ℂ) * z j).im := by
    rw [him]
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (hC j) (le_of_lt (hz j))
    · exact ⟨j0, Finset.mem_univ j0, mul_pos hj0 (hz j0)⟩
  intro hz0
  rw [hz0] at hpos'
  simp at hpos'

/-- **The row-linear product is real-stable** (the base of the Gurvits capacity iteration): for a
nonnegative matrix with strictly positive row sums (e.g. doubly stochastic), `∏ᵢ ∑ⱼ Aᵢⱼ Xⱼ` is
real-stable. -/
lemma rowLinearMvPolynomial_realStable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, 0 < ∑ j, A i j) :
    RealStable (ProofsInTheBook.Chapter22.rowLinearMvPolynomial A) := by
  rw [ProofsInTheBook.Chapter22.rowLinearMvPolynomial]
  apply RealStable.prod
  intro i _
  exact linearForm_stable (A i) (fun j => hA i j) (hrow i)

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







/-- For `m ≥ 1`, `G(m+1) = (m/(m+1))^m`. -/
lemma G_succ (m : ℕ) : G (m + 1) = ((m : ℝ) / (m + 1 : ℝ)) ^ m := by
  simp only [G, Nat.add_sub_cancel]
  norm_num

/-- **The Gurvits product telescopes to `n!/nⁿ`.**
`∏_{m=2}^{n} G(m) = n! / nⁿ`. -/
theorem gurvits_product_telescopes (n : ℕ) (hn : 1 ≤ n) :
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

/-- **Univariate Gurvits lemma (factored form).** If `C·t ≤ c·∏ᵢ(1+λᵢt)` for all `t>0`, with
`c, λᵢ ≥ 0` and `Σλ > 0` and `k ≥ 2`, then `G(k)·C ≤ c·Σλ`. (`c·Σλ` is the coefficient of `t`
in `c·∏(1+λᵢt)`.) This is the analytic crux of the Gurvits capacity reduction step. -/
lemma univariate_gurvits_factored {k : ℕ} (hk : 2 ≤ k) (c C : ℝ) (lam : Fin k → ℝ)
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



/-!
### Capacity lower-bound bookkeeping for the reduction chain

The analytic-free stable-polynomial step is most convenient to state as a
lower-bound invariant rather than as an actual infimum.  `CapLB p c` means that
`c` is a certified lower bound for the Gurvits capacity of `p`.
-/









lemma nonnegativeCoefficients_C {m : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    NonnegativeCoefficients (MvPolynomial.C c : MvPolynomial (Fin m) ℝ) := by
  classical
  intro a
  rw [MvPolynomial.coeff_C]
  split_ifs <;> positivity

lemma nonnegativeCoefficients_X {m : ℕ} (i : Fin m) :
    NonnegativeCoefficients (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) := by
  classical
  intro a
  rw [MvPolynomial.coeff_X']
  split_ifs <;> positivity

lemma NonnegativeCoefficients.add {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hq : NonnegativeCoefficients q) :
    NonnegativeCoefficients (p + q) := by
  intro a
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hp a) (hq a)

lemma NonnegativeCoefficients.mul {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hq : NonnegativeCoefficients q) :
    NonnegativeCoefficients (p * q) := by
  classical
  intro a
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (hp b.1) (hq b.2)

lemma nonnegativeCoefficients_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i ∈ s, NonnegativeCoefficients (f i)) :
    NonnegativeCoefficients (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro a
      simp
  | insert i s his ih =>
      simp_rw [Finset.sum_insert his]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma nonnegativeCoefficients_prod {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i ∈ s, NonnegativeCoefficients (f i)) :
    NonnegativeCoefficients (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact nonnegativeCoefficients_C (by positivity : (0 : ℝ) ≤ 1)
  | insert i s his ih =>
      simp_rw [Finset.prod_insert his]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma rowLinearMvPolynomial_nonnegativeCoefficients {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    NonnegativeCoefficients (rowLinearMvPolynomial A) := by
  classical
  rw [rowLinearMvPolynomial]
  apply nonnegativeCoefficients_prod
  intro i _
  apply nonnegativeCoefficients_sum
  intro j _
  exact (nonnegativeCoefficients_C (hA i j)).mul (nonnegativeCoefficients_X j)

lemma rowLinearMvPolynomial_isHomogeneous {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (rowLinearMvPolynomial A).IsHomogeneous n := by
  classical
  rw [rowLinearMvPolynomial]
  convert MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => ∑ j, MvPolynomial.C (A i j) * (MvPolynomial.X j : MvPolynomial (Fin n) ℝ))
    (fun _ => 1) ?_ using 1
  · simp
  · intro i _hi
    apply MvPolynomial.IsHomogeneous.sum
    intro j _hj
    exact MvPolynomial.isHomogeneous_C_mul_X (A i j) j





lemma coeff_mul_C_mul_X_of_pos {m : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (a : Fin m →₀ ℕ) (j : Fin m) (c : ℝ)
    (ha : a j ≠ 0) :
    MvPolynomial.coeff a (p * (MvPolynomial.C c * MvPolynomial.X j)) =
      MvPolynomial.coeff (a - Finsupp.single j 1) p * c := by
  have hsum : a - Finsupp.single j 1 + Finsupp.single j 1 = a :=
    Finsupp.sub_add_single_one_cancel ha
  rw [← hsum]
  rw [show p * (MvPolynomial.C c * MvPolynomial.X j) =
      MvPolynomial.C c * (p * MvPolynomial.X j) by ring]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X]
  have hsub : (a - Finsupp.single j 1 + Finsupp.single j 1) - Finsupp.single j 1 =
      a - Finsupp.single j 1 := by
    rw [hsum]
  rw [hsub]
  ring

lemma degree_sub_single_of_pos {m d : ℕ}
    (a : Fin m →₀ ℕ) (j : Fin m) (hdeg : a.degree = d + 1) (ha : a j ≠ 0) :
    (a - Finsupp.single j 1).degree = d := by
  have hsum : a - Finsupp.single j 1 + Finsupp.single j 1 = a :=
    Finsupp.sub_add_single_one_cancel ha
  have hdeg_sum := congrArg Finsupp.degree hsum
  simp [hdeg] at hdeg_sum
  omega

lemma exists_pos_apply_of_degree_pos {m : ℕ} (a : Fin m →₀ ℕ) (hdeg : 0 < a.degree) :
    ∃ j : Fin m, 0 < a j := by
  by_contra h
  push Not at h
  have hazero : a = 0 := by
    ext j
    exact Nat.eq_zero_of_le_zero (h j)
  rw [hazero] at hdeg
  simp at hdeg

lemma allDegreeCoefficientsPositive_one {m : ℕ} :
    AllDegreeCoefficientsPositive 0 (1 : MvPolynomial (Fin m) ℝ) := by
  intro a hdeg
  have ha0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp hdeg
  subst a
  simp

lemma allDegreeCoefficientsPositive_mul_positive_linear {m d : ℕ}
    {p : MvPolynomial (Fin m) ℝ} (hpnonneg : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive d p) (C : Fin m → ℝ) (hC : ∀ j, 0 < C j) :
    AllDegreeCoefficientsPositive (d + 1)
      (p * ∑ j, MvPolynomial.C (C j) * (MvPolynomial.X j : MvPolynomial (Fin m) ℝ)) := by
  intro a hdeg
  have hdegpos : 0 < a.degree := by rw [hdeg]; omega
  obtain ⟨j0, hj0pos⟩ := exists_pos_apply_of_degree_pos a hdegpos
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_pos'
  · intro j _hj
    exact (hpnonneg.mul ((nonnegativeCoefficients_C (le_of_lt (hC j))).mul
      (nonnegativeCoefficients_X j))) a
  · refine ⟨j0, Finset.mem_univ j0, ?_⟩
    rw [coeff_mul_C_mul_X_of_pos p a j0 (C j0) (ne_of_gt hj0pos)]
    exact mul_pos (hp _ (degree_sub_single_of_pos a j0 hdeg (ne_of_gt hj0pos))) (hC j0)

lemma product_positive_linear_allDegreeCoefficientsPositive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hApos : ∀ i j, 0 < A i j) (s : Finset (Fin n)) :
    AllDegreeCoefficientsPositive s.card
      (∏ i ∈ s, ∑ j, MvPolynomial.C (A i j) *
        (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (allDegreeCoefficientsPositive_one (m := n))
  | insert i s his ih =>
      rw [Finset.card_insert_of_notMem his]
      simp_rw [Finset.prod_insert his]
      rw [mul_comm]
      exact allDegreeCoefficientsPositive_mul_positive_linear
        (nonnegativeCoefficients_prod s
          (fun i => ∑ j, MvPolynomial.C (A i j) *
            (MvPolynomial.X j : MvPolynomial (Fin n) ℝ))
          (by
            intro i _hi
            apply nonnegativeCoefficients_sum
            intro j _hj
            exact (nonnegativeCoefficients_C (le_of_lt (hApos i j))).mul
              (nonnegativeCoefficients_X j)))
        ih (A i) (hApos i)

lemma rowLinearMvPolynomial_allDegreeCoefficientsPositive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hApos : ∀ i j, 0 < A i j) :
    AllDegreeCoefficientsPositive n (rowLinearMvPolynomial A) := by
  classical
  rw [rowLinearMvPolynomial]
  simpa using
    product_positive_linear_allDegreeCoefficientsPositive A hApos (Finset.univ : Finset (Fin n))



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





lemma squarefreeExponent_succ (m : ℕ) :
    Finsupp.cons 1 (squarefreeExponent m) = squarefreeExponent (m + 1) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [squarefreeExponent]
  · intro j
    simp [squarefreeExponent]

lemma finsupp_fin_one_eq_squarefree_of_degree_one (a : Fin 1 →₀ ℕ) (hdeg : a.degree = 1) :
    a = squarefreeExponent 1 := by
  apply Finsupp.ext
  intro j
  fin_cases j
  have h : a 0 = 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_one] using hdeg
  simp [squarefreeExponent, h]

lemma eval_one_eq_squarefreeCoeff_of_homogeneous_one
    {p : MvPolynomial (Fin 1) ℝ} (hhom : p.IsHomogeneous 1) :
    MvPolynomial.eval (fun _ : Fin 1 => (1 : ℝ)) p =
      MvPolynomial.coeff (squarefreeExponent 1) p := by
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (squarefreeExponent 1)]
  · simp
  · intro a _ha hne
    have hcoeff0 : MvPolynomial.coeff a p = 0 := by
      by_cases hdeg : a.degree = 1
      · exact False.elim (hne (finsupp_fin_one_eq_squarefree_of_degree_one a hdeg))
      · exact hhom.coeff_eq_zero hdeg
    rw [hcoeff0, zero_mul]
  · intro hnot
    rw [MvPolynomial.mem_support_iff] at hnot
    have hc0 : MvPolynomial.coeff (squarefreeExponent 1) p = 0 := not_not.mp hnot
    rw [hc0, zero_mul]









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

lemma sectionPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) (t : ℝ) :
    Polynomial.eval t (sectionPolynomial p x) =
      MvPolynomial.eval (Fin.cons t x) p := by
  simpa [sectionPolynomial] using
    (MvPolynomial.eval_eq_eval_mv_eval' (s := x) (y := t) (f := p)).symm



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

lemma sectionPolynomial_coeff_one {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) :
    Polynomial.coeff (sectionPolynomial p x) 1 =
      MvPolynomial.eval x (firstReduction p) := by
  simp [sectionPolynomial, firstReduction]





















































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

lemma firstReduction_realStable_of_allDegree {m : ℕ} (hm : 1 ≤ m)
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









lemma firstReduction_capLB_of_factoredSections {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ} {C : ℝ}
    (hm : 1 ≤ m)
    (hsections : PositiveFactoredSections p)
    (hcap : CapLB p C) :
    CapLB (firstReduction p) (G (m + 1) * C) := by
  intro x hx
  obtain ⟨c, lam, hc, hlam, hS, heval, hcoeff⟩ := hsections x hx
  have hbound :
      ∀ t : ℝ, 0 < t →
        (C * ∏ i, x i) * t ≤ c * ∏ i, (1 + lam i * t) := by
    intro t ht
    have hpos : PositiveVector (Fin.cons t x) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · exact ht
      · intro j
        exact hx j
    have h := hcap (Fin.cons t x) hpos
    rw [← sectionPolynomial_eval p x t, heval t] at h
    simpa [Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hstep :
      G (m + 1) * (C * ∏ i, x i) ≤ c * ∑ i, lam i :=
    univariate_gurvits_factored (k := m + 1) (by omega) c
      (C * ∏ i, x i) lam hc hlam hS hbound
  calc
    (G (m + 1) * C) * ∏ i, x i =
        G (m + 1) * (C * ∏ i, x i) := by ring
    _ ≤ c * ∑ i, lam i := hstep
    _ = Polynomial.coeff (sectionPolynomial p x) 1 := hcoeff.symm
    _ = MvPolynomial.eval x (firstReduction p) := sectionPolynomial_coeff_one p x

lemma rowLinear_capLB_one_of_capacity {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hcap : RowLinearCapacityAtLeastOne A) :
    CapLB (rowLinearMvPolynomial A) 1 := by
  intro x hx
  simpa [CapLB, PositiveVector, eval_rowLinearMvPolynomial, one_mul] using
    hcap.le_rowLinearProduct x hx

lemma row_sum_pos_of_nonnegative_of_capacity {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hcap : RowLinearCapacityAtLeastOne A) (i : Fin n) :
    0 < ∑ j, A i j := by
  have hx : PositiveVector (fun _ : Fin n => (1 : ℝ)) := by
    intro j
    positivity
  have h := hcap.le_rowLinearProduct (fun _ : Fin n => (1 : ℝ)) hx
  have hprod_ge_one : 1 ≤ ∏ i, ∑ j, A i j := by
    simpa [rowLinearProduct] using h
  have hprod_pos : 0 < ∏ i, ∑ j, A i j := by linarith
  have hrow_nonneg : 0 ≤ ∑ j, A i j :=
    Finset.sum_nonneg fun j _ => hA i j
  by_contra hnot
  have hrow_le_zero : ∑ j, A i j ≤ 0 := le_of_not_gt hnot
  have hrow_zero : ∑ j, A i j = 0 := le_antisymm hrow_le_zero hrow_nonneg
  have hprod_zero : (∏ i, ∑ j, A i j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hrow_zero
  linarith

lemma rowLinearMvPolynomial_realStable_of_capacity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hcap : RowLinearCapacityAtLeastOne A) :
    ProofsInTheBook.Chapter22Stable.RealStable (rowLinearMvPolynomial A) :=
  ProofsInTheBook.Chapter22Stable.rowLinearMvPolynomial_realStable A hA
    (row_sum_pos_of_nonnegative_of_capacity hA hcap)

theorem stable_allDegree_capacity_bound :
    ∀ (m : ℕ) (p : MvPolynomial (Fin m) ℝ) (C : ℝ), 1 ≤ m →
      NonnegativeCoefficients p →
      AllDegreeCoefficientsPositive m p →
      p.IsHomogeneous m →
      ProofsInTheBook.Chapter22Stable.RealStable p →
      CapLB p C →
      (∏ i ∈ Finset.Icc 2 m, G i) * C ≤
        MvPolynomial.coeff (squarefreeExponent m) p
  | 0, _p, _C, hm, _hpcoeff, _hpall, _hhom, _hstable, _hcap => by omega
  | 1, p, C, _hm, _hpcoeff, _hpall, hhom, _hstable, hcap => by
      have hx : PositiveVector (fun _ : Fin 1 => (1 : ℝ)) := by
        intro i
        fin_cases i
        positivity
      have h := hcap (fun _ : Fin 1 => (1 : ℝ)) hx
      simpa [eval_one_eq_squarefreeCoeff_of_homogeneous_one hhom] using h
  | m + 2, p, C, _hm, hpcoeff, hpall, hhom, hstable, hcap => by
      let p' : MvPolynomial (Fin (m + 1)) ℝ := firstReduction p
      have hm1 : 1 ≤ m + 1 := by omega
      have hsections : PositiveFactoredSections p :=
        positiveFactoredSections_of_realStable_allDegree hm1 hpcoeff hpall hhom hstable
      have hcap' : CapLB p' (G (m + 2) * C) := by
        exact firstReduction_capLB_of_factoredSections hm1 hsections hcap
      have hpcoeff' : NonnegativeCoefficients p' :=
        firstReduction_nonnegativeCoefficients hpcoeff
      have hpall' : AllDegreeCoefficientsPositive (m + 1) p' :=
        allDegreeCoefficientsPositive_firstReduction hpall
      have hhom' : p'.IsHomogeneous (m + 1) :=
        firstReduction_isHomogeneous hhom
      have hstable' : ProofsInTheBook.Chapter22Stable.RealStable p' :=
        firstReduction_realStable_of_allDegree hm1 hpcoeff hpall hhom hstable
      have ih := stable_allDegree_capacity_bound (m + 1) p' (G (m + 2) * C)
        hm1 hpcoeff' hpall' hhom' hstable' hcap'
      have hcoeff_eq :
          MvPolynomial.coeff (squarefreeExponent (m + 1)) p' =
            MvPolynomial.coeff (squarefreeExponent (m + 2)) p := by
        dsimp [p']
        rw [coeff_firstReduction, squarefreeExponent_succ]
      rw [← hcoeff_eq]
      calc
        (∏ i ∈ Finset.Icc 2 (m + 2), G i) * C =
            (∏ i ∈ Finset.Icc 2 (m + 1), G i) * (G (m + 2) * C) := by
              rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 2)]
              ring
        _ ≤ MvPolynomial.coeff (squarefreeExponent (m + 1)) p' := ih





/-!
### Algebraic interface to the Chapter 22 capacity core

The analytic Gurvits step should produce the lower bound with the telescoping
product of the constants `G(2), ..., G(n)`.  The theorem below is the purely
algebraic last mile: once that iterated capacity estimate is available for the
row-linear polynomial, the exact `n! / n^n` squarefree-coefficient core follows.
-/















theorem chapter22_positive (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ i j, 0 < A i j)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  by_cases hn0 : n = 0
  · subst n
    simpa using Chapter22.van_der_Waerden_permanent_fin_zero A hA
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hnonneg : ∀ i j, 0 ≤ A i j := fun i j => le_of_lt (hpos i j)
    have hcap : RowLinearCapacityAtLeastOne A :=
      rowLinearCapacityAtLeastOne_of_doublyStochastic A hA
    have hbound :
        (∏ i ∈ Finset.Icc 2 n, G i) ≤ rowLinearSquarefreeCoefficient A := by
      have h := stable_allDegree_capacity_bound n (rowLinearMvPolynomial A) 1 hn
        (rowLinearMvPolynomial_nonnegativeCoefficients A hnonneg)
        (rowLinearMvPolynomial_allDegreeCoefficientsPositive A hpos)
        (rowLinearMvPolynomial_isHomogeneous A)
        (rowLinearMvPolynomial_realStable_of_capacity A hnonneg hcap)
        (rowLinear_capLB_one_of_capacity hcap)
      simpa [rowLinearSquarefreeCoefficient] using h
    rw [rowLinearSquarefreeCoefficient_eq_permanent A] at hbound
    simpa [gurvits_product_telescopes n hn] using hbound

lemma permanent_tendsto_of_entrywise {n : ℕ}
    {B : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hentry : ∀ i j, Filter.Tendsto (fun N : ℕ => B N i j) Filter.atTop
      (nhds (A i j))) :
    Filter.Tendsto (fun N : ℕ => (B N).permanent) Filter.atTop (nhds A.permanent) := by
  classical
  unfold Matrix.permanent
  exact tendsto_finsetSum Finset.univ fun σ _ =>
    tendsto_finsetProd Finset.univ fun i _ => hentry (σ i) i



end

end ProofsInTheBook.Chapter22Gurvits

end


set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  by_cases hn0 : n = 0
  · subst n
    simpa using ProofsInTheBook.Chapter22.van_der_Waerden_permanent_fin_zero A hA
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    let θ : ℕ → ℝ := fun N => (((N + 1 : ℕ) : ℝ)⁻¹)
    let Aθ : ℕ → Matrix (Fin n) (Fin n) ℝ :=
      fun N => (1 - θ N) • A + θ N • flatDoublyStochasticMatrix n
    have hθ_pos : ∀ N, 0 < θ N := by
      intro N
      dsimp [θ]
      positivity
    have hθ_le_one : ∀ N, θ N ≤ 1 := by
      intro N
      have hden : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      simpa [θ] using inv_le_one_of_one_le₀ hden
    have hflat : flatDoublyStochasticMatrix n ∈ doublyStochastic ℝ (Fin n) :=
      flatDoublyStochasticMatrix_mem_doublyStochastic n
    have hAθ_ds : ∀ N, Aθ N ∈ doublyStochastic ℝ (Fin n) := by
      intro N
      have hleft : 0 ≤ 1 - θ N := sub_nonneg.mpr (hθ_le_one N)
      have hright : 0 ≤ θ N := le_of_lt (hθ_pos N)
      have hsum : (1 - θ N) + θ N = 1 := by ring
      simpa [Aθ] using
        (convex_doublyStochastic (R := ℝ) (n := Fin n)) hA hflat hleft hright hsum
    have hAθ_pos : ∀ N i j, 0 < Aθ N i j := by
      intro N i j
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hflat_pos : 0 < flatDoublyStochasticMatrix n i j := by
        simpa [flatDoublyStochasticMatrix] using inv_pos.mpr hnR
      have hAij : 0 ≤ A i j := nonneg_of_mem_doublyStochastic hA
      have hleft : 0 ≤ (1 - θ N) * A i j :=
        mul_nonneg (sub_nonneg.mpr (hθ_le_one N)) hAij
      have hright : 0 < θ N * flatDoublyStochasticMatrix n i j :=
        mul_pos (hθ_pos N) hflat_pos
      simpa [Aθ, Matrix.add_apply, Matrix.smul_apply] using add_pos_of_nonneg_of_pos hleft hright
    have hθ_tend : Filter.Tendsto θ Filter.atTop (nhds 0) := by
      simpa [θ] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hentry : ∀ i j, Filter.Tendsto (fun N : ℕ => Aθ N i j) Filter.atTop
        (nhds (A i j)) := by
      intro i j
      have hleft :
          Filter.Tendsto (fun N : ℕ => (1 - θ N) * A i j) Filter.atTop
            (nhds ((1 - 0) * A i j)) :=
        (tendsto_const_nhds.sub hθ_tend).mul tendsto_const_nhds
      have hright :
          Filter.Tendsto
            (fun N : ℕ => θ N * flatDoublyStochasticMatrix n i j) Filter.atTop
            (nhds (0 * flatDoublyStochasticMatrix n i j)) :=
        hθ_tend.mul tendsto_const_nhds
      simpa [Aθ, Matrix.add_apply, Matrix.smul_apply] using hleft.add hright
    have hperm_tend :
        Filter.Tendsto (fun N : ℕ => (Aθ N).permanent) Filter.atTop
          (nhds A.permanent) :=
      permanent_tendsto_of_entrywise hentry
    have hineq : ∀ N, (n.factorial : ℝ) / (n : ℝ) ^ n ≤ (Aθ N).permanent := by
      intro N
      exact chapter22_positive n (Aθ N) (hAθ_pos N) (hAθ_ds N)
    exact ge_of_tendsto hperm_tend (Filter.Eventually.of_forall hineq)
