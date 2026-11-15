-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_centered_projectedDifference_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.12466+00:00
-- url     : https://prove2.me/submissions/c65c5f06-2fb0-4f3e-b0a8-7e4250719998

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
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
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexTwoCopyCenteredCorrelation_eq_projected

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















end Wikipedia.SzemeredisTheorem

end
/-!
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Factor-independence of structural CFZ certificates -/
/-! ## Arbitrary simplex factors under homogeneous AP majorants -/
/-! ## Active-face cardinality and the comparison invariant -/
/-! ## Replacing one canonical edge by a whole-face function -/
/-! ## The exact mixed-copy strong-linear-forms interface -/

open Wikipedia.SzemeredisTheorem in
/-- Four homogeneous/mixed correlation estimates control the centered
second moment of the difference of the two projected weights. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    {ε : ℝ}
    (hHH :
      |simplexTwoCopyCenteredCorrelation n N ν
        (fun _ => H) j| ≤ ε)
    (hKK :
      |simplexTwoCopyCenteredCorrelation n N ν
        (fun _ => K) j| ≤ ε)
    (hcross :
      HasSparseDenseCrossCorrelationLe
        n N ν H K j ε) :
    |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          (generalSimplexProjectedWeight H j y -
            generalSimplexProjectedWeight K j y) ^ 2)| ≤
      4 * ε := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  have hHH' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          A y * A y)| ≤ ε := by
    rw [← simplexTwoCopyCenteredCorrelation_eq_projected
      n N ν (fun _ => H) j]
    exact hHH
  have hHK' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          A y * B y)| ≤ ε := by
    have h := hcross.1
    rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
    simpa [A, B, simplexCopyPair] using h
  have hKH' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          B y * A y)| ≤ ε := by
    have h := hcross.2
    rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
    simpa [A, B, simplexCopyPair] using h
  have hKK' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          B y * B y)| ≤ ε := by
    rw [← simplexTwoCopyCenteredCorrelation_eq_projected
      n N ν (fun _ => K) j]
    exact hKK
  have hexpand :
      mean (fun y =>
        apFaceCenteredCore n N ν j y *
          (A y - B y) ^ 2) =
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y) +
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y) := by
    rw [← mean_sub, ← mean_sub, ← mean_add]
    apply congrArg mean
    funext y
    ring
  rw [hexpand]
  calc
    |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y) +
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y)| ≤
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y)| := by
      calc
        |(mean (fun y =>
              apFaceCenteredCore n N ν j y * A y * A y) -
            mean (fun y =>
              apFaceCenteredCore n N ν j y * A y * B y) -
            mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * A y)) +
            mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| ≤
            |mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * A y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * B y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)| +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| :=
          abs_add_le _ _
        _ ≤
            (|mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * A y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * B y)| +
             |mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)|) +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| := by
          gcongr
          exact abs_sub _ _
        _ ≤
            ((|mean (fun y =>
                  apFaceCenteredCore n N ν j y * A y * A y)| +
               |mean (fun y =>
                  apFaceCenteredCore n N ν j y * A y * B y)|) +
             |mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)|) +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| := by
          gcongr
          exact abs_sub _ _
    _ ≤ ε + ε + ε + ε :=
      add_le_add
        (add_le_add (add_le_add hHH' hHK') hKH') hKK'
    _ = 4 * ε := by ring
