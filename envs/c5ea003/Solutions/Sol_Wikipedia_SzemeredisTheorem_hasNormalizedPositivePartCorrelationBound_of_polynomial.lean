-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasNormalizedPositivePartCorrelationBound_of_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:42.733426+00:00
-- url     : https://prove2.me/submissions/50f2d8f2-065e-4918-a9d9-b5f323d9ac0d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finitePairing_le_mul_mean_abs
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finitePairing_polynomial_eval_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finiteTestCombination_le_coefficientL1

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





theorem finitePairing_add_right
    {Ω : Type*} [Fintype Ω]
    (f q r : Ω → ℝ) :
    finitePairing f (q + r) =
      finitePairing f q + finitePairing f r := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
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









@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

















/-! ## Bounded combinations and approximation of positive part -/





/-- A normalized test combination takes values in `[-1,1]`. -/
theorem finiteTestCombination_mem_unitInterval
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    finiteTestCombination q c x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, ← abs_le]
  simpa [hc] using
    abs_finiteTestCombination_le_coefficientL1 hq c x





/-- Pointwise polynomial approximation after substituting a normalized test
combination. -/
theorem polynomial_eval_approximates_positivePart_combination
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ : ℝ}
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    |p.eval (finiteTestCombination q c x) -
        positivePart (finiteTestCombination q c) x| ≤ δ := by
  exact hp _ (finiteTestCombination_mem_unitInterval hq hc x)

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
/-! ## Bounded combinations and approximation of positive part -/
/-! ## Quantitative positive-part correlation -/

open Wikipedia.SzemeredisTheorem in
/-- Polynomial approximation plus monomial correlation estimates imply the
normalized positive-part correlation bound used by dense-model duality. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasNormalizedPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) := by
  intro c hc
  let Q := finiteTestCombination q c
  let P : Ω → ℝ := fun x => p.eval (Q x)
  have hpoly :
      finitePairing (ν - fun _ => 1) P ≤
        polynomialCoefficientL1 p * η := by
    exact le_trans (le_abs_self _) <|
      abs_finitePairing_polynomial_eval_le p c hc hmono
  have hpoint :
      ∀ x, |positivePart Q x - P x| ≤ δ := by
    intro x
    have hx :=
      polynomial_eval_approximates_positivePart_combination
        hq hp hc x
    simpa [Q, P, abs_sub_comm] using hx
  have herr0 :
      |finitePairing (ν - fun _ => 1)
        (positivePart Q - P)| ≤
          δ * centeredAbsoluteMean ν := by
    have hbase :=
      abs_finitePairing_le_mul_mean_abs
        (ν - fun _ => 1) (positivePart Q - P)
        (by
          intro x
          simpa using hpoint x)
    have hcentered :
        (fun x =>
          |(ν - (fun _ : Ω => (1 : ℝ))) x|) =
          (fun x => |ν x - 1|) := by
      funext x
      rfl
    rw [hcentered] at hbase
    exact hbase
  have herr :
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤ δ * M := by
    calc
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤
          |finitePairing (ν - fun _ => 1)
            (positivePart Q - P)| :=
        le_abs_self _
      _ ≤ δ * centeredAbsoluteMean ν := herr0
      _ ≤ δ * M :=
        mul_le_mul_of_nonneg_left hM hδ
  have hsplit :
      finitePairing (ν - fun _ => 1) (positivePart Q) =
        finitePairing (ν - fun _ => 1) P +
          finitePairing (ν - fun _ => 1)
            (positivePart Q - P) := by
    rw [← finitePairing_add_right]
    congr 1
    funext x
    simp
  rw [hsplit]
  exact add_le_add hpoly herr
