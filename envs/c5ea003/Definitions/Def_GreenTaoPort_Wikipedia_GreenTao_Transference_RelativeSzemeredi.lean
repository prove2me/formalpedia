-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:16:17.838549+00:00
-- url     : https://prove2.me/theorems/dc754d9b-a71e-48cc-98d3-8a376dade82c
-- title:
--   Polynomial dense-model errors and relative AP-count comparison
-- statement:
--   For a real polynomial $p$, cut error $c$, and approximation error $a$, the dense-model error is
--
--   $$
--   \|p\|_{\mathrm{coeff},1}\,c+a(2+c),
--   $$
--
--   where the coefficient norm is the sum of the absolute values of the polynomial coefficients.
--
--   At a positive cyclic modulus, the relative AP-comparison predicate requires that a nonnegative sparse weight $f\le\nu$ and a unit-bounded dense weight $g$ have $(r+2)$-term progression counts differing by at most the designated counting error whenever their $(r+1)$-coordinate cut discrepancy is at most the designated cut error. The majorant $\nu$ and the two error parameters are fixed before quantifying over $f,g$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeSzemeredi.lean#L28-L49

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Quantitative relative Szemerédi assembly

This file composes the parts of transference which do not depend on the
remaining sparse-simplex comparison.

* Cut discrepancy against the constant tests retains the mean of the sparse
  weight in its dense model.
* A uniform weighted Szemerédi theorem gives a positive lower bound for the
  dense model's progression count.
* Any quantitative relative-counting comparison then transfers that lower
  bound back to the sparse weight.

The final theorem plugs in the polynomial dense-model theorem obtained from
the ordinary CFZ linear-forms condition.  Its only unproved analytic input
is named explicitly by `RelativeAPComparisonLe`; no asymptotic or
pseudorandomness assertion is hidden in this module.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Polynomial

/-- The explicit cut-discrepancy error produced by the polynomial
dense-model theorem. -/
noncomputable def polynomialDenseModelError
    (p : ℝ[X]) (cutError approximationError : ℝ) : ℝ :=
  polynomialCoefficientL1 p * cutError +
    approximationError * (2 + cutError)

/-- Quantitative relative counting at progression length `r + 2`.

The sparse weight is only assumed nonnegative and bounded by `ν`; the dense
model is pointwise in `[0,1]`.  This is exactly the comparison theorem left
to the recursive densification argument. -/
def RelativeAPComparisonLe
    (r N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (cutError countError : ℝ) : Prop :=
  ∀ (f g : ZMod N → ℝ),
    (∀ x, 0 ≤ f x) →
    (∀ x, f x ≤ ν x) →
    IsUnitBounded g →
    CutDiscrepancyLe (r + 1) f g cutError →
    |cyclicAPCount (r + 2) N f -
        cyclicAPCount (r + 2) N g| ≤ countError









end Wikipedia.SzemeredisTheorem


