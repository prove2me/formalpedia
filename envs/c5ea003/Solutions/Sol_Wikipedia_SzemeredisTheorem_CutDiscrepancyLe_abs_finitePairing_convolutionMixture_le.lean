-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.CutDiscrepancyLe.abs_finitePairing_convolutionMixture_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:26.464331+00:00
-- url     : https://prove2.me/submissions/630b3004-a379-4b97-a6cd-cfce05a40de5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_ConvolutionMixture_finitePairing_eval
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fiberConvolution_pairing_succ
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fiberConvolution_pairing_zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl



























theorem CutDiscrepancyLe.apply_bounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε)
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    |cutCorrelation r f g u| ≤ ε :=
  h u hu.nonneg hu.le_one

































end Wikipedia.SzemeredisTheorem

end

section


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl























































/-- Exact disintegration over the coordinate-sum map, including arity zero. -/
theorem fiberConvolution_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution r w z) := by
  cases r with
  | zero => exact fiberConvolution_pairing_zero w h
  | succ n => exact fiberConvolution_pairing_succ n w h





/-- A cut correlation is exactly the pairing of `f-g` with its generalized
convolution. -/
theorem cutCorrelation_eq_mean_mul_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      mean (fun z : G =>
        (f z - g z) * generalizedConvolution r u z) := by
  exact fiberConvolution_pairing r (cutTestProduct u)
    (fun z => f z - g z)

end Wikipedia.SzemeredisTheorem

end
/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
universe u
/-! ## Finite convex mixtures -/
/-! ## Consequences for dense-model moments -/

open Wikipedia.SzemeredisTheorem.CutDiscrepancyLe in
/-- Cut discrepancy controls the pairing with every finite convolution
mixture. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe r ν (fun _ => 1) ε)
    (m : ConvolutionMixture G r) :
    |finitePairing (ν - fun _ => 1) m.eval| ≤ ε := by
  let : Fintype m.ι := m.indexFintype
  let : Nonempty m.ι := m.indexNonempty
  rw [m.finitePairing_eval]
  calc
    |mean (fun a : m.ι =>
        finitePairing (ν - fun _ => 1)
          (generalizedConvolution r (m.tests a)))| ≤
        mean (fun a : m.ι =>
          |finitePairing (ν - fun _ => 1)
            (generalizedConvolution r (m.tests a))|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : m.ι => ε) := by
      apply mean_mono
      intro a
      have ha :=
        hcut.apply_bounded (m.tests a) (m.bounded a)
      rw [cutCorrelation_eq_mean_mul_generalizedConvolution] at ha
      simpa [finitePairing] using ha
    _ = ε := mean_const _
