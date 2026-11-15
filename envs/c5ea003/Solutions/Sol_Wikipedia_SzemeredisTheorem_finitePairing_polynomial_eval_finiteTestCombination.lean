-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.finitePairing_polynomial_eval_finiteTestCombination
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:01.86622+00:00
-- url     : https://prove2.me/submissions/8d5c22b7-0f4f-49ac-935d-5c6ff1cbc612

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_polynomial_eval_finiteTestCombination

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise













theorem finitePairing_smul_right
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing f (c • q) = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring









































































































































end Wikipedia.SzemeredisTheorem

end

section



/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/











/-- Pairing commutes with a finite sum in its right input. -/
theorem finitePairing_finset_sum_right
    {Ω κ : Type*} [Fintype Ω]
    (f : Ω → ℝ) (s : Finset κ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i ∈ s, q i x) =
      ∑ i ∈ s, finitePairing f (q i) := by
  classical
  unfold finitePairing mean
  calc
    (𝔼 x, f x * ∑ i ∈ s, q i x) =
        𝔼 x, ∑ i ∈ s, f x * q i x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, 𝔼 x, f x * q i x := by
      exact Finset.expect_sum_comm Finset.univ s _

/-- Pairing commutes with a sum over a finite type in its right input. -/
theorem finitePairing_fintype_sum_right
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (f : Ω → ℝ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i, q i x) =
      ∑ i, finitePairing f (q i) := by
  simpa using finitePairing_finset_sum_right f Finset.univ q













/-! ## Bounded combinations and approximation of positive part -/













/-! ## Quantitative positive-part correlation -/













end Wikipedia.SzemeredisTheorem

end
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite products and polynomial expansions -/

open Wikipedia.SzemeredisTheorem in
/-- Exact expansion after pairing a polynomial in a test combination with
an arbitrary function. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (p : ℝ[X])
    (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f
        (fun x => p.eval (finiteTestCombination q c x)) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing f (testMonomial q s) := by
  classical
  have heval :
      (fun x => p.eval (finiteTestCombination q c x)) =
        fun x => ∑ n ∈ p.support,
          ∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              testMonomial q s x := by
    funext x
    exact polynomial_eval_finiteTestCombination p q c x
  rw [heval, finitePairing_finset_sum_right]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finitePairing_fintype_sum_right]
  apply Fintype.sum_congr
  intro s
  change
    finitePairing f
        ((p.coeff n * ∏ i, c (s i)) • testMonomial q s) =
      _
  exact
    finitePairing_smul_right
      (p.coeff n * ∏ i, c (s i)) f (testMonomial q s)
