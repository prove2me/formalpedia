-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.apTwoCopyHeterogeneousMasked_iterNext_hasCFZCertificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:57:46.587683+00:00
-- url     : https://prove2.me/submissions/fefa5628-077a-4a14-8f89-defd01e53763

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_HasCFZCertificate_reindex
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_HasCFZTerminal_iterNext
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZTerminal
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_iterNext_next_eq_iterNext_succ_reindex
import Theorems.Thm_Wikipedia_SzemeredisTheorem_iterNextDecoded_apTwoCopyHeterogeneousMasked_majorant_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_iterNextDecoded_headMajorantMean_eq_orderedCubeMean

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
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators























/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h







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
# Stage decoders for relative-counting Cauchy--Schwarz recursion

Repeated applications of `MajorizedCutSystem.next` replace an external
parameter `P` by the left-associated tower

`(((P × (G × G)) × (G × G)) × ⋯)`.

The declarations below give this tower a stable stage-indexed name and
identify it with a base parameter together with a Boolean pair for every
coordinate already eliminated.  In the AP application the base parameter
is itself a Boolean pair, belonging to the distinguished omitted face.
Thus stage `r` is canonically a Boolean cube on `r + 1` axes.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The nested parameter tower -/





















/-! ## Boolean-axis form of the AP parameter -/







/-! ## Full AP cube decoder -/

















/-! ## Expected CFZ selectors at a decoded stage -/













/-! ## Iterating `MajorizedCutSystem.next` -/

namespace MajorizedCutSystem











/-- Reindexing the finite external parameter does not change the majorant
moment paid at the next Cauchy--Schwarz step. -/
theorem reindex_headMajorantMean
    {P Q G : Type u}
    [Fintype P] [Fintype Q] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (e : Q ≃ P) :
    (S.reindex e).headMajorantMean =
      S.headMajorantMean := by
  unfold headMajorantMean mean₂ reindex
  apply mean_equiv e
  intro q
  rfl















/-- Decoding the nested stage parameter preserves its next paid moment. -/
theorem iterNextDecoded_headMajorantMean
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G ((n + 1) + r)) :
    (iterNextDecoded S).headMajorantMean =
      (iterNext r S).headMajorantMean :=
  reindex_headMajorantMean
    (iterNext r S)
    (csStageParamEquiv P G r).symm







end MajorizedCutSystem

/-! ## Quantitative endpoint after the decoded first stage -/



end Wikipedia.SzemeredisTheorem

end

section


/-!
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem



















/-- Transporting an arity forth and back is definitionally harmless. -/
theorem castArity_symm
    {P G : Type u} {m n : ℕ}
    (h : m = n)
    (S : MajorizedCutSystem P G m) :
    castArity h.symm (castArity h S) = S := by
  subst n
  rfl























end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/



















namespace MajorizedCutSystem

























end MajorizedCutSystem

/-! ## Quantitative active-mask endpoint -/



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





/-- The decoded successor paid moment is an ordinary CFZ subproduct with
the copy-aware stage selector. -/
theorem iterNextDecoded_apTwoCopyHeterogeneousMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (MajorizedCutSystem.iterNextDecoded
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j)) := by
  rw [
    iterNextDecoded_headMajorantMean_eq_orderedCubeMean
      r s N j]
  apply congrArg mean
  funext x
  exact
    iterNextDecoded_apTwoCopyHeterogeneousMasked_majorant_zero
      r s N ν active g j hrest x

/-- The same paid-moment identity for the native nested `next` tower. -/
theorem iterNext_apTwoCopyHeterogeneousMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (MajorizedCutSystem.iterNext r
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j)) := by
  rw [←
    MajorizedCutSystem.iterNextDecoded_headMajorantMean
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)]
  exact
    iterNextDecoded_apTwoCopyHeterogeneousMasked_headMajorantMean
      r s N ν active g j hrest

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
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- Every copy-aware paid stage moment, together with the terminal
identity, assembles into a structural certificate at an arbitrary point of
the native `iterNext` tower. -/
theorem solution
    (k r s N : ℕ) [NeZero N]
    (hk : k = s + r)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (k + 1) → Bool)
    (g : Bool → APFaceWeightFamily k N)
    (j : Fin (k + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    HasCFZCertificate ν j
      (iterNext r
        (castArity hk
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            k N ν active g j hrest))) := by
  induction s generalizing k r with
  | zero =>
      subst k
      have hterminal :=
        apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZTerminal
          (0 + r) N ν active g j hrest
      have hstage :=
        hterminal.iterNext j r 0
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            (0 + r) N ν active g j hrest)
      change
        HasCFZTerminal ν j
          (iterNext r
            (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
              (0 + r) N ν active g j hrest))
      exact hstage
  | succ s ih =>
      subst k
      let S :=
        apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest
      change
        HasCFZCertificate ν j
          (iterNext r S)
      refine
        ⟨apCSHeterogeneousOrderedStageFaceExponent
            r s active j,
          ?_, ?_⟩
      · exact
          iterNext_apTwoCopyHeterogeneousMasked_headMajorantMean
            r s N ν active g j hrest
      · have hk' :
            (s + 1) + r = s + (r + 1) := by
          omega
        have htail :
            HasCFZCertificate ν j
              (iterNext (r + 1)
                (castArity hk' S)) :=
          ih ((s + 1) + r) (r + 1) hk'
            active g j hrest
        have hrelRaw :=
          iterNext_next_eq_iterNext_succ_reindex
            s r (castArity hk' S)
        have hround :
            castArity
                (show s + (r + 1) =
                    (s + 1) + r by omega)
                (castArity hk' S) =
              S := by
          simpa only [] using
            castArity_symm hk' S
        have hrel :
            (iterNext r S).next =
              (iterNext (r + 1)
                (castArity hk' S)).reindex
                  (csStageAppendPairEquiv
                    (Bool → ZMod N) (ZMod N) r) := by
          rw [hround] at hrelRaw
          exact hrelRaw
        rw [hrel]
        exact htail.reindex j
          (iterNext (r + 1)
            (castArity hk' S))
          (csStageAppendPairEquiv
            (Bool → ZMod N) (ZMod N) r)
