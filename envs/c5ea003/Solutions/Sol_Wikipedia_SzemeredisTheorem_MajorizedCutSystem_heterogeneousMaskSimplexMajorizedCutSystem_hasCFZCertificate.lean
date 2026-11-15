-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.heterogeneousMaskSimplexMajorizedCutSystem_hasCFZCertificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:00:31.326257+00:00
-- url     : https://prove2.me/submissions/3f471627-3e7a-443d-a24c-7c1bba082085

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_HasCFZCertificate_of_core_and_majorant_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZCertificate

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





























































end Wikipedia.SzemeredisTheorem

end

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

section


/-!
# Heterogeneous AP-simplex densification states

The one-colour calculation in `RelativeDensification` uses one common
function on every non-distinguished AP face.  This file performs the same
calculation for a family of face weights `g i`.  For a chosen colour `j`,
the product of all other colours is averaged over the missing `j`
coordinate, then truncated at one on the actual deleted-face space
`Fin n → ZMod N`.

The final section packages the full simplex count and the resulting
lower-arity pairing as two different constructors of one payload type.  In
particular, the projected state is not falsely identified with another
`(n + 1)`-colour AP simplex.  It records the bounded surrogate on its real
domain and separately transports all untouched pointwise majorant bounds
along `j.succAbove`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Heterogeneous AP face systems -/





@[simp]
theorem apHeterogeneousSimplexSystem_edge
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (i : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apHeterogeneousSimplexSystem n N g).edgeWeight i x =
      g i (apSimplexForm (n + 1) N i x) :=
  rfl



















/-! ## Projection bounds -/













/-! ## Exact heterogeneous count and pairing -/













/-! ## A concrete full-to-projected state transition -/































namespace RelativeDensificationIteration



end RelativeDensificationIteration











end Wikipedia.SzemeredisTheorem

end

section


/-!
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The copy-dependent AP cut system -/



@[simp]
theorem apCopyMaskedFaceMajorant_apply
    {k N : ℕ}
    (ν : ZMod N → ℝ)
    (active : Bool → Fin k → Bool)
    (b : Bool) (i : Fin k) (z : ZMod N) :
    apCopyMaskedFaceMajorant ν active b i z =
      if active b i then ν z else 1 :=
  rfl





/-! ## Copy-aware recursive stage selectors -/





/-! ## Copy-aware paid stage moments -/









/-! ## Copy-aware terminal selector -/







namespace MajorizedCutSystem

















end MajorizedCutSystem

/-! ## Quantitative correlation bounds -/



















/-! ## Arbitrary weighted-simplex factors -/

namespace MajorizedCutSystem



end MajorizedCutSystem

















namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary-factor quantitative bridge -/









namespace HasLinearFormsCondition







end HasLinearFormsCondition

end Wikipedia.SzemeredisTheorem

end
/-!
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## The copy-dependent AP cut system -/
/-! ## Copy-aware recursive stage selectors -/
/-! ## Copy-aware paid stage moments -/
/-! ## Copy-aware terminal selector -/
/-! ## Quantitative correlation bounds -/
/-! ## Arbitrary weighted-simplex factors -/
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- The copy-dependent AP certificate is insensitive to replacing its AP
pullback factors by arbitrary nonnegative weighted-simplex factors below
the same designated majorants. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Bool → Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x) :
    HasCFZCertificate ν j
      (heterogeneousMaskSimplexMajorizedCutSystem
        n N ν active H j hrest) := by
  have hmajorant :
      ∀ b,
        APUntouchedFaceBounds
          (apCopyMaskedFaceMajorant ν active b)
          (apCopyMaskedFaceMajorant ν active b) j := by
    intro b t z
    constructor
    · unfold apCopyMaskedFaceMajorant
      unfold apMaskedFaceMajorant
      split
      · exact hν z
      · exact zero_le_one
    · exact le_rfl
  let T :=
    apTwoCopyHeterogeneousMaskedMajorizedCutSystem
      n N ν active
        (apCopyMaskedFaceMajorant ν active) j hmajorant
  apply HasCFZCertificate.of_core_and_majorant_eq
    j
    (S := heterogeneousMaskSimplexMajorizedCutSystem
      n N ν active H j hrest)
    (T := T)
  · intro a y
    rfl
  · intro a t z
    rfl
  · exact
      apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZCertificate
        n N ν active
          (apCopyMaskedFaceMajorant ν active) j hmajorant
