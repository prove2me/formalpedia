-- Prove2me | Definitions.Def_P2MAssembly_Chapter22
-- name    : P2MAssembly_Chapter22
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T17:02:46.249921+00:00
-- url     : https://prove2.me/theorems/79dcfcac-2de8-443b-9621-7c9668dff418
-- title:
--   Row products, capacity bounds, real stability, and factored sections
-- statement:
--   For a real square matrix A, the row-product polynomial is
--   $$p_A(x)=\prod_i\left(\sum_j A_{ij}x_j\right).$$
--   The bundle defines its evaluation, its coefficient of the squarefree monomial $\prod_j x_j$, and separately the permutation sum $\sum_{\sigma}\prod_i A_{i,\sigma(i)}$. The flat matrix has every entry $1/n$. Capacity at least one means $\prod_j x_j\leq p_A(x)$ for every strictly positive vector x; more generally, $\mathrm{CapLB}(p,c)$ means $c\prod_j x_j\leq p(x)$ on this positive orthant.
--
--   A real multivariate polynomial is real stable if its complex evaluation never vanishes when every coordinate has strictly positive imaginary part; the zero polynomial does not satisfy this definition. NonnegativeCoefficients requires every coefficient to be nonnegative. AllDegreeCoefficientsPositive(d,p) requires strict positivity for every monomial of total degree d, including indices outside the support. Homogeneity is a separate premise in theorems that need it. The first reduction is $[x_0^1]p$, equivalently the derivative in the distinguished variable evaluated at zero. Real and complex section polynomials specialize the remaining variables, complex line sections substitute $a_j+b_jT$, and the distinguished derivative can also be evaluated at a complex value c.
--
--   For a real univariate polynomial q, RealRooted is the equality between the number of real roots counted with multiplicity and the natural degree; under these conventions the zero polynomial also satisfies that equality. Finite root enumerations retain multiplicities. FactoredSectionData(k,q) consists of $c\geq0$ and $\lambda_i\geq0$ with $\sum_i\lambda_i>0$, together with both identities
--   $$q(t)=c\prod_{i=1}^k(1+\lambda_i t)\quad(t\in\mathbb R),\qquad [t]q=c\sum_i\lambda_i.$$
--   PositiveFactoredSections supplies such data with k=m+1 for every strictly positive specialization of the remaining m variables. The Gurvits factor is $G(k)=((k-1)/k)^{k-1}$, with real division and natural exponent $k-1$ interpreted using Lean’s conventions at k=0.
--
--   The retained bundle also contains proved supporting results about coefficients, specializations, real roots, and limits. In particular, closure of the lower-half-plane root condition is proved for coefficientwise convergent sequences with fixed degree, with the limit having that same degree and being nonzero. Factorizations of positive sections are constructed under the stated coefficient, degree, and real-rootedness or stability hypotheses. These are conditional mathematical infrastructure; the definition bundle does not assume the permanent lower bound as a field or axiom.
-- source:
--   Original repository definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22.lean#L54 (flat matrix and row products), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Stable.lean#L20 (real stability), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Stable.lean#L98 (real-rootedness), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L166 (coefficient and capacity predicates), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L377 (first reduction), and https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L965 (factored section data). Topic: Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture” (https://doi.org/10.1007/978-3-662-57265-8_24). All assembly original source files match the cited public commit byte-for-byte.

import Init
import Mathlib

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

def flatDoublyStochasticMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => (n : ℝ)⁻¹







/-- Row-linear product `∏ᵢ ∑ⱼ Aᵢⱼ xⱼ`, the polynomial used in Gurvits's
stable-polynomial proof of Van der Waerden's conjecture. -/
def rowLinearProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, ∑ j, A i j * x j

/-- The same row-linear product as a multivariate polynomial. -/
def rowLinearMvPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j



/-- The exponent vector of the squarefree monomial `∏ⱼ xⱼ`. -/
def squarefreeExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- The squarefree coefficient of `∏ᵢ ∑ⱼ Aᵢⱼ xⱼ`. -/
def rowLinearSquarefreeCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  MvPolynomial.coeff (squarefreeExponent n) (rowLinearMvPolynomial A)

/--
The mixed coefficient of the row-linear product, written as the sum over
choosing one column in each row and requiring that every column is chosen once.
This is the coefficient of the squarefree monomial `∏ⱼ xⱼ` in the expanded
row-linear product.
-/
def rowLinearMixedCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)





















/--
The capacity lower bound needed for the row-linear product:
`∏ⱼ xⱼ ≤ ∏ᵢ ∑ⱼ Aᵢⱼ xⱼ` on the positive orthant.  For a doubly stochastic
matrix this follows from weighted AM-GM plus the column-sum equations.
-/
structure RowLinearCapacityAtLeastOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  le_rowLinearProduct :
    ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → ∏ j, x j ≤ rowLinearProduct A x























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

/-- A real multivariate polynomial is real-stable if it is nonzero whenever every variable lies
in the open upper half-plane. -/
def RealStable {m : ℕ} (p : MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ z : Fin m → ℂ, (∀ i, 0 < (z i).im) →
    MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0









/-!
### Univariate real-rootedness and its derivative closure (the univariate Lieb–Sokal heart)

A univariate real polynomial is real-rooted iff it splits over ℝ — equivalently its root multiset
(with multiplicity) has cardinality equal to its degree. The derivative of a real-rooted polynomial
is again real-rooted (Rolle's theorem / interlacing). This is the one-variable case of the stability
closure; the full multivariate Lieb–Sokal lemma (`∂/∂xₘ` preserves real-stability) lifts it via the
Hurwitz theorem and remains the genuine remaining analytic input for the Gurvits reduction.
-/

open Polynomial in
/-- A univariate real polynomial is real-rooted: all roots real (splits over ℝ), i.e. the root
multiset cardinality equals the degree. -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

open Polynomial in
/-- **A real polynomial with no root in the open upper half-plane is real-rooted**
(conjugate-pairing: a non-real root would have a conjugate in the upper half-plane). This is the
bridge from univariate real-stability to real-rootedness, used in the Lieb–Sokal lifting. -/
lemma realRooted_of_forall_uhp_ne_zero (q : ℝ[X])
    (h : ∀ w : ℂ, 0 < w.im → Polynomial.aeval w q ≠ 0) : RealRooted q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [RealRooted]
  rw [RealRooted, ← Polynomial.splits_iff_card_roots]
  apply Polynomial.Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _)
  intro a ha
  have haroot : Polynomial.aeval a q = 0 := by
    have h2 := (Polynomial.mem_roots'.mp ha).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at h2
  have him : a.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hconj : Polynomial.aeval ((starRingEnd ℂ) a) q = 0 := by
        rw [Polynomial.aeval_conj, haroot, map_zero]
      have hconjim : 0 < ((starRingEnd ℂ) a).im := by
        rw [Complex.conj_im]; linarith
      exact h _ hconjim hconj
    · exact h a hpos haroot
  refine ⟨a.re, ?_⟩
  apply Complex.ext
  · simp
  · simp [him]







open Polynomial in
/-- **Cauchy root bound**: every root of a nonzero complex polynomial satisfies
`‖z‖ ≤ 1 + (Σ_{i<d} ‖coeff i‖) / ‖leadingCoeff‖`. Needed for the compactness step of the
root-continuity (Hurwitz-specialization) argument. -/
lemma norm_root_le_one_add (q : Polynomial ℂ) (hq : q ≠ 0) {z : ℂ} (hz : q.IsRoot z) :
    ‖z‖ ≤ 1 + (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) / ‖q.leadingCoeff‖ := by
  set d := q.natDegree with hd
  set L := ‖q.leadingCoeff‖ with hL
  set S := ∑ i ∈ Finset.range d, ‖q.coeff i‖ with hS
  have hLpos : 0 < L := by
    rw [hL]; exact norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  by_contra hcon
  push_neg at hcon
  have hz1 : 1 < ‖z‖ := by
    have h0 : 0 ≤ S / L := div_nonneg hSnn (le_of_lt hLpos)
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  -- a nonzero constant has no root, so d ≥ 1
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hpos
    · exfalso
      have hconst : q.eval z = q.coeff 0 := by
        rw [Polynomial.eval_eq_sum_range, ← hd, hd0]
        simp
      have hc0 : q.coeff 0 = q.leadingCoeff := by
        rw [Polynomial.leadingCoeff, ← hd, hd0]
      have hzero := hz
      rw [Polynomial.IsRoot, hconst, hc0] at hzero
      exact (Polynomial.leadingCoeff_ne_zero.mpr hq) hzero
    · exact hpos
  -- split the evaluation: leading term + lower terms
  have heval := hz
  rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range, ← hd, Finset.sum_range_succ] at heval
  have hcd : q.coeff d = q.leadingCoeff := by rw [Polynomial.leadingCoeff, hd]
  have h1 : q.leadingCoeff * z ^ d = -(∑ i ∈ Finset.range d, q.coeff i * z ^ i) := by
    rw [← hcd]
    linear_combination heval
  -- norm estimate: L‖z‖^d ≤ S‖z‖^(d-1)
  have hmain : L * ‖z‖ ^ d ≤ S * ‖z‖ ^ (d - 1) := by
    have h2 : ‖q.leadingCoeff * z ^ d‖ = L * ‖z‖ ^ d := by
      rw [norm_mul, norm_pow, hL]
    rw [← h2, h1, norm_neg]
    calc ‖∑ i ∈ Finset.range d, q.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range d, ‖q.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range d, ‖q.coeff i‖ * ‖z‖ ^ i := by
          simp [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range d, ‖q.coeff i‖ * ‖z‖ ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ d - 1 := by
            have := Finset.mem_range.mp hi; omega
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (le_of_lt hz1) hile) (norm_nonneg _)
      _ = S * ‖z‖ ^ (d - 1) := by rw [← Finset.sum_mul, hS]
  -- divide by ‖z‖^(d-1) > 0 to get L‖z‖ ≤ S
  have hpowsplit : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpowsplit] at hmain
  have hzd : 0 < ‖z‖ ^ (d - 1) := pow_pos hzpos _
  have hLz : L * ‖z‖ ≤ S := by
    nlinarith [hmain, hzd]
  have hfin : ‖z‖ ≤ S / L := (le_div_iff₀ hLpos).mpr (by linarith)
  linarith

noncomputable section

lemma multiset_enum_toList {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d) :
    Multiset.map (fun i : Fin d =>
      s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i))
      Finset.univ.val = s := by
  rw [Fin.univ_val_map]
  have hlen : s.toList.length = d := by rw [Multiset.length_toList, hcard]
  change (List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) :
    Multiset α) = s
  have hlist :
      List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) = s.toList := by
    exact (List.ofFn_congr hlen (s.toList.get)).symm.trans (List.ofFn_get s.toList)
  exact (congrArg (fun l : List α => (l : Multiset α)) hlist).trans (Multiset.coe_toList s)

lemma multiset_enum_toList_mem {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d)
    (i : Fin d) :
    s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈ s := by
  have hmem : s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈
      s.toList := List.get_mem _ _
  rwa [Multiset.mem_toList] at hmem

lemma continuous_esymm_fin (d j : ℕ) :
    Continuous fun v : Fin d → ℂ => (Finset.univ.val.map v).esymm j := by
  have hfun : (fun v : Fin d → ℂ => (Finset.univ.val.map v).esymm j)
      = fun v : Fin d → ℂ => ∑ t ∈ Finset.univ.powersetCard j, ∏ i ∈ t, v i := by
    funext v
    exact Finset.esymm_map_val v Finset.univ j
  rw [hfun]
  exact continuous_finsetSum _ (fun t _ =>
    continuous_finsetProd _ (fun i _ => continuous_apply i))

lemma continuous_prod_roots_coeff_fin {d k : ℕ} (hk : k ≤ d) :
    Continuous fun v : Fin d → ℂ =>
      ((Finset.univ.val.map v).map (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k := by
  have hfun : (fun v : Fin d → ℂ =>
        ((Finset.univ.val.map v).map (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k)
      = fun v : Fin d → ℂ => (-1 : ℂ) ^ (d - k) * (Finset.univ.val.map v).esymm (d - k) := by
    funext v
    rw [Multiset.prod_X_sub_C_coeff]
    · simp
    · simpa using hk
  rw [hfun]
  exact continuous_const.mul (continuous_esymm_fin d (d - k))

lemma roots_im_nonpos_of_tendsto (d : ℕ) (q : ℕ → Polynomial ℂ) (qlim : Polynomial ℂ)
    (hdeg : ∀ n, (q n).natDegree = d) (hdeglim : qlim.natDegree = d) (hlim0 : qlim ≠ 0)
    (hcoeff : ∀ k, Filter.Tendsto (fun n => (q n).coeff k) Filter.atTop (nhds (qlim.coeff k)))
    (hroots : ∀ n, ∀ z ∈ (q n).roots, z.im ≤ 0) :
    ∀ z ∈ qlim.roots, z.im ≤ 0 := by
  classical
  by_cases hd0 : d = 0
  · have hconst : qlim.roots = 0 := by
      have hqconst : qlim = Polynomial.C (qlim.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hd0] using hdeglim)
      rw [hqconst]
      simp
    intro z hz
    rw [hconst] at hz
    simpa using hz
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hqnz : ∀ n, q n ≠ 0 := by
    intro n hn
    have := hdeg n
    rw [hn, Polynomial.natDegree_zero] at this
    omega
  have hleadlim_ne : qlim.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hlim0
  have hcoefflim_d_ne : qlim.coeff d ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hdeglim] using hleadlim_ne
  have hcard : ∀ n, (q n).roots.card = d := by
    intro n
    exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (q n))).trans (hdeg n)
  let r : ℕ → Fin d → ℂ := fun n i =>
    (q n).roots.toList.get
      (Fin.cast (((Multiset.length_toList (q n).roots).trans (hcard n)).symm) i)
  have henum : ∀ n, Finset.univ.val.map (r n) = (q n).roots := by
    intro n
    simpa [r] using multiset_enum_toList ((q n).roots) (hcard n)
  have hrmem : ∀ n i, r n i ∈ (q n).roots := by
    intro n i
    simpa [r] using multiset_enum_toList_mem ((q n).roots) (hcard n) i
  let L : ℝ := ‖qlim.coeff d‖
  have hLpos : 0 < L := by
    simp [L, hcoefflim_d_ne]
  let S : ℝ := ∑ k ∈ Finset.range d, (‖qlim.coeff k‖ + 1)
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => by positivity
  let B : ℝ := 1 + S / (L / 2)
  have hhalfpos : 0 < L / 2 := by positivity
  have hBnonneg : 0 ≤ B := by
    have hdiv_nonneg : 0 ≤ S / (L / 2) := div_nonneg hSnonneg hhalfpos.le
    dsimp [B]
    linarith
  have hlead_event : ∀ᶠ n in Filter.atTop, L / 2 ≤ ‖(q n).leadingCoeff‖ := by
    have hnorm : Filter.Tendsto (fun n => ‖(q n).coeff d‖) Filter.atTop (nhds L) := by
      simpa [L] using (hcoeff d).norm
    have hev : ∀ᶠ n in Filter.atTop, L / 2 < ‖(q n).coeff d‖ :=
      hnorm.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    have hcd : (q n).coeff d = (q n).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg n]
    rw [← hcd]
    exact le_of_lt hn
  have hlow_event :
      ∀ᶠ n in Filter.atTop, ∀ k ∈ Finset.range d, ‖(q n).coeff k‖ ≤ ‖qlim.coeff k‖ + 1 := by
    rw [Filter.eventually_all_finset]
    intro k _
    have hnorm : Filter.Tendsto (fun n => ‖(q n).coeff k‖) Filter.atTop
        (nhds ‖qlim.coeff k‖) := (hcoeff k).norm
    exact (hnorm.eventually (gt_mem_nhds (by linarith))).mono fun _ hn => le_of_lt hn
  have hbound_event : ∀ᶠ n in Filter.atTop, ∀ i : Fin d, ‖r n i‖ ≤ B := by
    filter_upwards [hlead_event, hlow_event] with n hlead hlow i
    have hroot_isRoot : (q n).IsRoot (r n i) := (Polynomial.mem_roots'.mp (hrmem n i)).2
    have hcauchy := norm_root_le_one_add (q n) (hqnz n) hroot_isRoot
    have hcauchy' :
        ‖r n i‖ ≤
          1 + (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) / ‖(q n).leadingCoeff‖ := by
      simpa [hdeg n] using hcauchy
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range d, ‖(q n).coeff k‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsum_le : (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) ≤ S := by
      dsimp [S]
      exact Finset.sum_le_sum fun k hk => hlow k hk
    have hfrac :
        (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) / ‖(q n).leadingCoeff‖
          ≤ S / (L / 2) :=
      div_le_div₀ hSnonneg hsum_le hhalfpos hlead
    exact hcauchy'.trans (by dsimp [B]; linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound_event
  let box : Set (Fin d → ℂ) := {v | ∀ i : Fin d, ‖v i‖ ≤ B}
  have hbox_bdd : Bornology.IsBounded box := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℂ)) (r := B)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hBnonneg).2 hv
  let x : ℕ → (Fin d → ℂ) := fun n => r (n + N)
  have hxmem : ∀ n, x n ∈ box := by
    intro n i
    exact hN (n + N) (Nat.le_add_left N n) i
  obtain ⟨s, _hs_closure, φ, hφmono, hφlim⟩ := tendsto_subseq_of_bounded hbox_bdd hxmem
  have hs_im_nonpos : ∀ i : Fin d, (s i).im ≤ 0 := by
    intro i
    have him_tendsto :
        Filter.Tendsto (fun n => (r (φ n + N) i).im) Filter.atTop (nhds (s i).im) := by
      simpa [x, Function.comp_def] using
        ((Complex.continuous_im.comp (continuous_apply i)).tendsto s).comp hφlim
    exact le_of_tendsto him_tendsto
      (Filter.Eventually.of_forall fun n =>
        hroots (φ n + N) (r (φ n + N) i) (hrmem (φ n + N) i))
  have hfactor : ∀ n,
      q n = Polynomial.C (q n).leadingCoeff *
        ((Finset.univ.val.map (r n)).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    intro n
    calc
      q n = Polynomial.C (q n).leadingCoeff *
          (((q n).roots).map (fun t => Polynomial.X - Polynomial.C t)).prod :=
        (IsAlgClosed.splits (q n)).eq_prod_roots
      _ = Polynomial.C (q n).leadingCoeff *
          ((Finset.univ.val.map (r n)).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
        rw [← henum n]
  let pstar : Polynomial ℂ :=
    Polynomial.C qlim.leadingCoeff *
      ((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod
  have hψ_tendsto : Filter.Tendsto (fun n => φ n + N) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat N).comp hφmono.tendsto_atTop
  have hidentify : qlim = pstar := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ d
    · have hqcoeff_tendsto :
          Filter.Tendsto (fun n => (q (φ n + N)).coeff k) Filter.atTop (nhds (qlim.coeff k)) :=
        (hcoeff k).comp hψ_tendsto
      have hlead_tendsto :
          Filter.Tendsto (fun n => (q (φ n + N)).leadingCoeff) Filter.atTop
            (nhds qlim.leadingCoeff) := by
        have hcd : Filter.Tendsto (fun n => (q (φ n + N)).coeff d) Filter.atTop
            (nhds (qlim.coeff d)) := (hcoeff d).comp hψ_tendsto
        have hcd' : Filter.Tendsto (fun n => (q (φ n + N)).leadingCoeff) Filter.atTop
            (nhds (qlim.coeff d)) := by
          exact hcd.congr (fun n => by rw [Polynomial.leadingCoeff, hdeg (φ n + N)])
        have hlead_eq : qlim.coeff d = qlim.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hdeglim]
        simpa [hlead_eq] using hcd'
      have hprod_tendsto :
          Filter.Tendsto
            (fun n => (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))
            Filter.atTop
            (nhds (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k)) := by
        simpa [x, Function.comp_def] using
          (continuous_prod_roots_coeff_fin (d := d) (k := k) hk).tendsto s |>.comp hφlim
      have hmul_tendsto :
          Filter.Tendsto
            (fun n => (q (φ n + N)).leadingCoeff *
              (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))
            Filter.atTop
            (nhds (qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))) :=
        hlead_tendsto.mul hprod_tendsto
      have hcoeff_factor : ∀ n,
          (q (φ n + N)).coeff k =
            (q (φ n + N)).leadingCoeff *
              (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k) := by
        intro n
        have h := congrArg (fun p : Polynomial ℂ => p.coeff k) (hfactor (φ n + N))
        simpa [Polynomial.coeff_C_mul] using h
      have hmul_as_q :
          Filter.Tendsto (fun n => (q (φ n + N)).coeff k) Filter.atTop
            (nhds (qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))) :=
        hmul_tendsto.congr' (Filter.Eventually.of_forall fun n => (hcoeff_factor n).symm)
      have heq :
          qlim.coeff k =
            qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k) :=
        tendsto_nhds_unique hqcoeff_tendsto hmul_as_q
      dsimp [pstar]
      rw [Polynomial.coeff_C_mul]
      exact heq
    · have hklt : d < k := Nat.lt_of_not_ge hk
      have hleft : qlim.coeff k = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hdeglim] using hklt)
      have hprod_natDegree :
          (((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod).natDegree = d := by
        rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
        simp
      have hprod_coeff0 :
          (((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod).coeff k = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [hprod_natDegree]
          exact hklt)
      have hright : pstar.coeff k = 0 := by
        dsimp [pstar]
        rw [Polynomial.coeff_C_mul, hprod_coeff0, mul_zero]
      rw [hleft, hright]
  intro z hz
  have hroot_eq : qlim.roots = Finset.univ.val.map s := by
    rw [hidentify]
    dsimp [pstar]
    rw [Polynomial.roots_C_mul _ hleadlim_ne, Polynomial.roots_multiset_prod_X_sub_C]
  rw [hroot_eq] at hz
  rcases Multiset.mem_map.mp hz with ⟨i, _hi, rfl⟩
  exact hs_im_nonpos i



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

/-- Gurvits capacity-reduction constant `G(k) = ((k-1)/k)^{k-1}`, with `G(0)=G(1)=1`. -/
noncomputable def G (k : ℕ) : ℝ := ((k - 1 : ℝ) / (k : ℝ)) ^ (k - 1)









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

def NonnegativeCoefficients {m : ℕ} (p : MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ a : Fin m →₀ ℕ, 0 ≤ MvPolynomial.coeff a p

def PositiveVector {m : ℕ} (x : Fin m → ℝ) : Prop :=
  ∀ i, 0 < x i

def CapLB {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin m → ℝ, PositiveVector x → c * ∏ i, x i ≤ MvPolynomial.eval x p

def AllDegreeCoefficientsPositive {m : ℕ} (d : ℕ) (p : MvPolynomial (Fin m) ℝ) :
    Prop :=
  ∀ a : Fin m →₀ ℕ, a.degree = d → 0 < MvPolynomial.coeff a p

















lemma eval_nonneg_of_nonnegativeCoefficients {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (hp a) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

lemma eval_pos_of_nonnegativeCoefficients {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hp_ne : p ≠ 0)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) :
    0 < MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_pos'
  · intro a ha
    exact mul_nonneg (hp a) (Finset.prod_nonneg fun i _ => pow_nonneg (le_of_lt (hx i)) _)
  · obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hp_ne
    refine ⟨a, ha, ?_⟩
    have hcoeff_ne : MvPolynomial.coeff a p ≠ 0 := MvPolynomial.mem_support_iff.mp ha
    have hcoeff_pos : 0 < MvPolynomial.coeff a p :=
      lt_of_le_of_ne (hp a) (Ne.symm hcoeff_ne)
    exact mul_pos hcoeff_pos (Finset.prod_pos fun i _ => pow_pos (hx i) _)















def firstReduction {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ) :
    MvPolynomial (Fin m) ℝ :=
  Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) 1







lemma degree_cons {m : ℕ} (k : ℕ) (a : Fin m →₀ ℕ) :
    (Finsupp.cons k a).degree = k + a.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.degree_eq_sum]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]



lemma coeff_finSuccEquiv_nonnegativeCoefficients {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) (i : ℕ) :
    NonnegativeCoefficients (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) i) := by
  intro a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  exact hp _











def sectionPolynomial {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ m p)

def complexSectionPolynomial {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (z : Fin m → ℂ) : Polynomial ℂ :=
  Polynomial.map (MvPolynomial.eval z)
    (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))

def complexLineSection {m : ℕ} (q : MvPolynomial (Fin m) ℂ)
    (a b : Fin m → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) q



















def distinguishedDerivativeAt {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (c : ℂ) : MvPolynomial (Fin m) ℂ :=
  Polynomial.eval (MvPolynomial.C c)
    (Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))))













lemma complexSectionPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (z : Fin m → ℂ) (t : ℂ) :
    Polynomial.eval t (complexSectionPolynomial p z) =
      MvPolynomial.eval (Fin.cons t z) (p.map (algebraMap ℝ ℂ)) := by
  simpa [complexSectionPolynomial] using
    (MvPolynomial.eval_eq_eval_mv_eval' (s := z) (y := t)
      (f := p.map (algebraMap ℝ ℂ))).symm





lemma complexSectionPolynomial_no_uhp_root {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : ProofsInTheBook.Chapter22Stable.RealStable p)
    {z : Fin m → ℂ} (hz : ∀ i, 0 < (z i).im) :
    ∀ w : ℂ, 0 < w.im → Polynomial.eval w (complexSectionPolynomial p z) ≠ 0 := by
  intro w hw
  rw [complexSectionPolynomial_eval]
  exact hp (Fin.cons w z) (by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hw
    · intro j
      exact hz j)





lemma sectionPolynomial_coeff_nonneg {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    0 ≤ Polynomial.coeff (sectionPolynomial p x) k := by
  rw [sectionPolynomial, Polynomial.coeff_map]
  exact eval_nonneg_of_nonnegativeCoefficients
    (coeff_finSuccEquiv_nonnegativeCoefficients hp k) hx



lemma coeff_zero_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) :
    (∏ i ∈ s, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 0 = 1 := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.prod_insert his]
      rw [Polynomial.mul_coeff_zero, ih]
      simp

lemma coeff_one_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) :
    (∏ i ∈ s, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 =
      ∑ i ∈ s, lam i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (Polynomial.coeff_one (R := ℝ) (n := 1))
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his]
      rw [Polynomial.mul_coeff_one, ih, coeff_zero_prod_one_add_mul_X s lam]
      have hcoeff_one : (1 : Polynomial ℝ).coeff 1 = 0 := by
        simpa using (Polynomial.coeff_one (R := ℝ) (n := 1))
      simp [hcoeff_one]
      ring

lemma coeff_one_C_mul_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ℝ) (lam : ι → ℝ) :
    (Polynomial.C c * ∏ i ∈ s,
        (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 =
      c * ∑ i ∈ s, lam i := by
  rw [Polynomial.coeff_C_mul, coeff_one_prod_one_add_mul_X]

lemma root_neg_of_nonnegative_coefficients_of_coeff_zero_pos {q : Polynomial ℝ}
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) (h0 : 0 < q.coeff 0)
    {r : ℝ} (hr : r ∈ q.roots) :
    r < 0 := by
  have hroot : q.IsRoot r := (Polynomial.mem_roots'.mp hr).2
  by_contra hnot
  have hr_nonneg : 0 ≤ r := le_of_not_gt hnot
  have hsum_pos :
      0 < ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * r ^ i := by
    apply Finset.sum_pos'
    · intro i _hi
      exact mul_nonneg (hcoeff i) (pow_nonneg hr_nonneg i)
    · refine ⟨0, ?_, ?_⟩
      · simp
      · simpa using h0
  have heval : q.eval r = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * r ^ i :=
    Polynomial.eval_eq_sum_range r
  have hzero : q.eval r = 0 := by
    simpa [Polynomial.IsRoot] using hroot
  linarith

lemma roots_enum_toList {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d) :
    Multiset.map (fun i : Fin d =>
      s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i))
      Finset.univ.val = s := by
  rw [Fin.univ_val_map]
  have hlen : s.toList.length = d := by rw [Multiset.length_toList, hcard]
  change (List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) :
    Multiset α) = s
  have hlist :
      List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) = s.toList := by
    exact (List.ofFn_congr hlen (s.toList.get)).symm.trans (List.ofFn_get s.toList)
  exact (congrArg (fun l : List α => (l : Multiset α)) hlist).trans (Multiset.coe_toList s)

lemma roots_enum_toList_mem {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d)
    (i : Fin d) :
    s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈ s := by
  have hmem : s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈
      s.toList := List.get_mem _ _
  rwa [Multiset.mem_toList] at hmem

structure FactoredSectionData (k : ℕ) (q : Polynomial ℝ) where
  c : ℝ
  lam : Fin k → ℝ
  c_nonneg : 0 ≤ c
  lam_nonneg : ∀ i, 0 ≤ lam i
  sum_lam_pos : 0 < ∑ i, lam i
  eval_eq : ∀ t : ℝ, Polynomial.eval t q = c * ∏ i, (1 + lam i * t)
  coeff_one_eq : Polynomial.coeff q 1 = c * ∑ i, lam i

noncomputable def rootsAsFin (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree)
    (i : Fin q.natDegree) : ℝ :=
  q.roots.toList.get
    (Fin.cast (((Multiset.length_toList q.roots).trans hcard).symm) i)

lemma rootsAsFin_mem (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree)
    (i : Fin q.natDegree) :
    rootsAsFin q hcard i ∈ q.roots := by
  simpa [rootsAsFin] using roots_enum_toList_mem q.roots hcard i

lemma rootsAsFin_enum (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree) :
    Finset.univ.val.map (rootsAsFin q hcard) = q.roots := by
  simpa [rootsAsFin] using roots_enum_toList q.roots hcard

lemma polynomialCoeff_finSuccEquiv_ne_zero_of_allDegree {m k : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (a : Fin m →₀ ℕ) (hdeg : k + a.degree = m + 1) :
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k ≠ 0 := by
  intro hzero
  have hcoeff_pos :
      0 < MvPolynomial.coeff a (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k) := by
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    exact hp (Finsupp.cons k a) (by rw [degree_cons, hdeg])
  rw [hzero] at hcoeff_pos
  simp at hcoeff_pos

lemma sectionPolynomial_coeff_pos_of_allDegree {m k : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x)
    (a : Fin m →₀ ℕ) (hdeg : k + a.degree = m + 1) :
    0 < (sectionPolynomial p x).coeff k := by
  rw [sectionPolynomial, Polynomial.coeff_map]
  exact eval_pos_of_nonnegativeCoefficients
    (coeff_finSuccEquiv_nonnegativeCoefficients hpcoeff k)
    (polynomialCoeff_finSuccEquiv_ne_zero_of_allDegree hp a hdeg) hx

lemma sectionPolynomial_const_coeff_pos_of_allDegree {m : ℕ}
    (hm : 1 ≤ m) {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    0 < (sectionPolynomial p x).coeff 0 := by
  let j0 : Fin m := ⟨0, by omega⟩
  let a : Fin m →₀ ℕ := Finsupp.single j0 (m + 1)
  exact sectionPolynomial_coeff_pos_of_allDegree hpcoeff hp hx a (by simp [a])

lemma sectionPolynomial_top_coeff_pos_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    0 < (sectionPolynomial p x).coeff (m + 1) := by
  exact sectionPolynomial_coeff_pos_of_allDegree hpcoeff hp hx 0 (by simp)

lemma sectionPolynomial_natDegree_eq_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    (sectionPolynomial p x).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine Polynomial.natDegree_map_le.trans ?_
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree p 0).trans hhom.totalDegree_le
  · exact ne_of_gt (sectionPolynomial_top_coeff_pos_of_allDegree hpcoeff hp hx)

lemma isHomogeneous_zero_eq_C_coeff_zero_complex {m : ℕ} {p : MvPolynomial (Fin m) ℂ}
    (hp : p.IsHomogeneous 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  · have hdeg_ne : a.degree ≠ 0 := by
      intro hdeg
      exact ha ((Finsupp.degree_eq_zero_iff a).mp hdeg)
    have h0a : ¬ (0 : Fin m →₀ ℕ) = a := fun h => ha h.symm
    rw [hp.coeff_eq_zero hdeg_ne]
    simp [h0a]

lemma complexSectionPolynomial_top_coeff_ne_zero_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (z : Fin m → ℂ) :
    (complexSectionPolynomial p z).coeff (m + 1) ≠ 0 := by
  let topPoly : MvPolynomial (Fin m) ℂ :=
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) (m + 1)
  have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
    simpa using hhom.map (algebraMap ℝ ℂ)
  have htopHom : topPoly.IsHomogeneous 0 := by
    dsimp [topPoly]
    simpa using hhomC.finSuccEquiv_coeff_isHomogeneous (m + 1) 0 (by omega)
  have htop0_ne : MvPolynomial.coeff 0 topPoly ≠ 0 := by
    dsimp [topPoly]
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (hp (Finsupp.cons (m + 1) 0) (by simp [degree_cons])))
  rw [complexSectionPolynomial, Polynomial.coeff_map]
  change MvPolynomial.eval z topPoly ≠ 0
  rw [isHomogeneous_zero_eq_C_coeff_zero_complex htopHom]
  simpa using htop0_ne

lemma complexSectionPolynomial_natDegree_eq_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (z : Fin m → ℂ) :
    (complexSectionPolynomial p z).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine Polynomial.natDegree_map_le.trans ?_
    rw [MvPolynomial.natDegree_finSuccEquiv]
    have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
      simpa using hhom.map (algebraMap ℝ ℂ)
    exact (MvPolynomial.degreeOf_le_totalDegree (p.map (algebraMap ℝ ℂ)) 0).trans
      hhomC.totalDegree_le
  · exact complexSectionPolynomial_top_coeff_ne_zero_of_allDegree hp hhom z

lemma coeff_finSuccEquiv_map_complex {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (k : ℕ) :
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) k =
      (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k).map (algebraMap ℝ ℂ) := by
  ext a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]

lemma complexSectionPolynomial_ofReal {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin m → ℝ) :
    complexSectionPolynomial p (fun j => (x j : ℂ)) =
      (sectionPolynomial p x).map (algebraMap ℝ ℂ) := by
  ext k
  simp [complexSectionPolynomial, sectionPolynomial, Polynomial.coeff_map,
    coeff_finSuccEquiv_map_complex]
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.map_eval (q := algebraMap ℝ ℂ) (g := x)
    (p := ((MvPolynomial.finSuccEquiv ℝ m) p).coeff k)).symm

lemma complexSectionPolynomial_coeff_tendsto {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) {zN : ℕ → Fin m → ℂ} {z : Fin m → ℂ}
    (hz : Filter.Tendsto zN Filter.atTop (nhds z)) (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => (complexSectionPolynomial p (zN N)).coeff k)
      Filter.atTop (nhds ((complexSectionPolynomial p z).coeff k)) := by
  simp [complexSectionPolynomial, Polynomial.coeff_map]
  exact ((MvPolynomial.continuous_eval
    (Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) k)).tendsto z).comp hz

lemma tendsto_upper_perturb {m : ℕ} (x : Fin m → ℝ) :
    Filter.Tendsto
      (fun N : ℕ => fun j : Fin m => (x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I)
      Filter.atTop (nhds (fun j : Fin m => (x j : ℂ))) := by
  rw [tendsto_pi_nhds]
  intro j
  have hepsR : Filter.Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)⁻¹ : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
      Filter.atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsR
  simpa using (tendsto_const_nhds.add (hepsC.mul tendsto_const_nhds))

lemma upper_perturb_im_pos {m : ℕ} (x : Fin m → ℝ) (N : ℕ) (j : Fin m) :
    0 < ((x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I).im := by
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_I_im]
  rw [Complex.inv_re]
  have hpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hnorm : 0 < Complex.normSq ((((N + 1 : ℕ) : ℝ) : ℂ)) := by
    exact Complex.normSq_pos.mpr (by exact_mod_cast ne_of_gt hpos)
  exact div_pos hpos hnorm

lemma sectionPolynomial_realRooted_of_realStable_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (x : Fin m → ℝ) :
    ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x) := by
  let zN : ℕ → Fin m → ℂ := fun N j =>
    (x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I
  let z0 : Fin m → ℂ := fun j => (x j : ℂ)
  let qN : ℕ → Polynomial ℂ := fun N => complexSectionPolynomial p (zN N)
  let q0 : Polynomial ℂ := complexSectionPolynomial p z0
  have hzN : Filter.Tendsto zN Filter.atTop (nhds z0) := by
    simpa [zN, z0] using tendsto_upper_perturb x
  have hdegN : ∀ N, (qN N).natDegree = m + 1 := by
    intro N
    exact complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom (zN N)
  have hdeg0 : q0.natDegree = m + 1 :=
    complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom z0
  have hq0_ne : q0 ≠ 0 := by
    intro hzero
    have := hdeg0
    rw [hzero, Polynomial.natDegree_zero] at this
    omega
  have hcoeff : ∀ k, Filter.Tendsto (fun N : ℕ => (qN N).coeff k) Filter.atTop
      (nhds (q0.coeff k)) := by
    intro k
    exact complexSectionPolynomial_coeff_tendsto p hzN k
  have hrootsN : ∀ N, ∀ w ∈ (qN N).roots, w.im ≤ 0 := by
    intro N w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    exact complexSectionPolynomial_no_uhp_root hstable
      (fun j => upper_perturb_im_pos x N j) w hwpos
      (by simpa [qN, zN, Polynomial.IsRoot] using hroot)
  have hroots0 : ∀ w ∈ q0.roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.roots_im_nonpos_of_tendsto (m + 1) qN q0
      hdegN hdeg0 hq0_ne hcoeff hrootsN
  apply ProofsInTheBook.Chapter22Stable.realRooted_of_forall_uhp_ne_zero
  intro w hw hzero
  have hzero_eval : Polynomial.eval w q0 = 0 := by
    dsimp [q0, z0]
    rw [complexSectionPolynomial_ofReal]
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hzero
  have hmem : w ∈ q0.roots :=
    Polynomial.mem_roots'.mpr ⟨hq0_ne, by simpa [Polynomial.IsRoot] using hzero_eval⟩
  have := hroots0 w hmem
  linarith











noncomputable def factoredSectionData_natDegree_of_realRooted_nonnegative {q : Polynomial ℝ}
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) (h0 : 0 < q.coeff 0)
    (hrooted : ProofsInTheBook.Chapter22Stable.RealRooted q)
    (hdeg_pos : 0 < q.natDegree) :
    FactoredSectionData q.natDegree q := by
  classical
  have hq_ne : q ≠ 0 := by
    intro hq
    rw [hq] at h0
    simp at h0
  have hsplits : q.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    exact hrooted
  have hcard : q.roots.card = q.natDegree := hrooted
  let r : Fin q.natDegree → ℝ := rootsAsFin q hcard
  let lam : Fin q.natDegree → ℝ := fun i => - (r i)⁻¹
  have hr_mem : ∀ i, r i ∈ q.roots := by
    intro i
    exact rootsAsFin_mem q hcard i
  have hr_neg : ∀ i, r i < 0 := by
    intro i
    exact root_neg_of_nonnegative_coefficients_of_coeff_zero_pos hcoeff h0 (hr_mem i)
  have hr_ne : ∀ i, r i ≠ 0 := fun i => (hr_neg i).ne
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    dsimp [lam]
    have hinv : (r i)⁻¹ < 0 := by
      simpa using (inv_lt_zero.mpr (hr_neg i))
    linarith
  have hroots_enum : Finset.univ.val.map r = q.roots := by
    simpa [r] using rootsAsFin_enum q hcard
  have heval_roots : ∀ t : ℝ, q.eval t = q.leadingCoeff * ∏ i, (t - r i) := by
    intro t
    have h := hsplits.eval_eq_prod_roots t
    rw [← hroots_enum] at h
    simpa [Finset.prod, Multiset.map_map, Function.comp_def] using h
  have hconst : q.coeff 0 = q.leadingCoeff * ∏ i, (-r i) := by
    have h0eval := heval_roots 0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using h0eval
  have heval_factored : ∀ t : ℝ,
      q.eval t = q.coeff 0 * ∏ i, (1 + lam i * t) := by
    intro t
    have hfactor_each : ∀ i : Fin q.natDegree,
        t - r i = (-r i) * (1 + lam i * t) := by
      intro i
      dsimp [lam]
      field_simp [hr_ne i]
      ring
    have hprod :
        (∏ i, (t - r i)) = (∏ i, (-r i)) * ∏ i, (1 + lam i * t) := by
      simp_rw [hfactor_each]
      rw [Finset.prod_mul_distrib]
    rw [heval_roots t, hprod, hconst]
    ring
  refine
    ⟨q.coeff 0, lam, le_of_lt h0, (fun i => le_of_lt (hlam_pos i)), ?_, ?_, ?_⟩
  · haveI : Nonempty (Fin q.natDegree) := ⟨⟨0, hdeg_pos⟩⟩
    exact Finset.sum_pos (fun i _ => hlam_pos i) Finset.univ_nonempty
  · exact heval_factored
  · have hpoly :
        q = Polynomial.C (q.coeff 0) *
          ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ) := by
      apply Polynomial.funext
      intro t
      calc
        q.eval t = q.coeff 0 * ∏ i, (1 + lam i * t) := heval_factored t
        _ = Polynomial.eval t
            (Polynomial.C (q.coeff 0) *
              ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)) := by
              have hprod_eval :
                  Polynomial.eval t
                    (∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)) =
                    ∏ i, (1 + lam i * t) := by
                rw [Polynomial.eval_prod]
                simp
              rw [Polynomial.eval_mul, Polynomial.eval_C, hprod_eval]
    calc
      q.coeff 1 =
          (Polynomial.C (q.coeff 0) *
            ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 :=
        congrArg (fun p : Polynomial ℝ => p.coeff 1) hpoly
      _ = q.coeff 0 * ∑ i, lam i :=
        coeff_one_C_mul_prod_one_add_mul_X
          (Finset.univ : Finset (Fin q.natDegree)) (q.coeff 0) lam

def PositiveFactoredSections {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ) : Type :=
  ∀ x : Fin m → ℝ, PositiveVector x →
    FactoredSectionData (m + 1) (sectionPolynomial p x)

noncomputable def positiveFactoredSections_of_realRooted_sections {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hrooted :
      ∀ x : Fin m → ℝ, PositiveVector x →
        ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x))
    (hconst :
      ∀ x : Fin m → ℝ, PositiveVector x →
        0 < (sectionPolynomial p x).coeff 0)
    (hdegree :
      ∀ x : Fin m → ℝ, PositiveVector x →
        (sectionPolynomial p x).natDegree = m + 1) :
    PositiveFactoredSections p := by
  intro x hx
  have hcoeff : ∀ n : ℕ, 0 ≤ (sectionPolynomial p x).coeff n := by
    intro n
    exact sectionPolynomial_coeff_nonneg hpcoeff (fun i => le_of_lt (hx i)) n
  have hdeg_pos : 0 < (sectionPolynomial p x).natDegree := by
    rw [hdegree x hx]
    omega
  simpa [hdegree x hx] using
    factoredSectionData_natDegree_of_realRooted_nonnegative
      (q := sectionPolynomial p x) hcoeff (hconst x hx) (hrooted x hx) hdeg_pos

noncomputable def positiveFactoredSections_of_realStable_allDegree {m : ℕ}
    (hm : 1 ≤ m) {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p) :
    PositiveFactoredSections p :=
  positiveFactoredSections_of_realRooted_sections hpcoeff
    (fun x _hx => sectionPolynomial_realRooted_of_realStable_allDegree hstable hp hhom x)
    (fun _x hx => sectionPolynomial_const_coeff_pos_of_allDegree hm hpcoeff hp hx)
    (fun _x hx => sectionPolynomial_natDegree_eq_of_allDegree hpcoeff hp hhom hx)















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


