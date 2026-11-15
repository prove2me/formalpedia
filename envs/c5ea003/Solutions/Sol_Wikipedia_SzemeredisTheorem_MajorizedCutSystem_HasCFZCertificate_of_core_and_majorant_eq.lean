-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.HasCFZCertificate.of_core_and_majorant_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:40:00.613821+00:00
-- url     : https://prove2.me/submissions/cb7f5477-cfb4-4815-aaaa-650da7478309

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
# CFZ certificates for projected two-copy correlations

The active-majorant induction in relative counting produces a two-copy
correlation.  The coordinate on the selected face is shared, while the
omitted simplex coordinate has two independent copies.  This file realizes
that correlation as a `MajorizedCutSystem`.

The first part supplies a reusable terminal-value theorem for systems whose
designated majorants are all one.  It identifies the fully iterated
Cauchy--Schwarz endpoint with the box moment of the original core.  Applied
to the centered AP face, the box moment is exactly `faceCenteredProduct`.

The second part defines the concrete two-copy AP cut factors and proves that
their system form is the projected correlation occurring in densification.
For factors bounded by one this gives an explicit, kernel-checked
`HasCFZCertificate`, and hence plugs the exact projected expression into the
weighted Cauchy--Schwarz API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem

/-! ## Terminal values for unit-majorant systems -/





/-- The core field of `next`, exposed uniformly across its two
dimension-pattern branches. -/
@[simp]
theorem next_core_apply
    {P G : Type*} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : G × G) (y : Fin n → G) :
    S.next.core (p, a) y =
      S.majorant p 0 y *
        S.core p (Fin.cons a.1 y) *
        S.core p (Fin.cons a.2 y) := by
  cases n <;> rfl





end MajorizedCutSystem

/-! ## The centered AP face as a box core -/





namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## Concrete two-copy AP cut factors -/













/-! ## A single paid active face -/

















/-! ## Mixed active-majorant system -/













/-! ## The bounded two-copy certificate -/













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

/-- Structural certificates depend on the core and designated majorants,
not on the particular dominated nonnegative factors. -/
theorem solution
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      {S T : MajorizedCutSystem P G n},
      (∀ p x, S.core p x = T.core p x) →
      (∀ p i x, S.majorant p i x =
        T.majorant p i x) →
      HasCFZCertificate ν j T →
      HasCFZCertificate ν j S := by
  intro P instP n
  induction n generalizing P with
  | zero =>
      intro S T hcore _hmajorant hT
      rcases hT with ⟨other, hother, hform⟩
      refine ⟨other, hother, ?_⟩
      rw [show S.form = T.form by
        unfold form
        apply congrArg mean
        funext p
        apply congrArg mean
        funext x
        simpa using hcore p x]
      exact hform
  | succ n ih =>
      intro S T hcore hmajorant hT
      rcases hT with ⟨e, hmoment, hnext⟩
      refine ⟨e, ?_, ?_⟩
      · rw [show S.headMajorantMean =
          T.headMajorantMean by
          unfold headMajorantMean mean₂
          apply congrArg mean
          funext p
          apply congrArg mean
          funext x
          exact hmajorant p 0 x]
        exact hmoment
      · apply ih
          (S := S.next) (T := T.next)
          (fun q x => ?_)
          (fun q i x => ?_)
          hnext
        · rw [next_core_apply, next_core_apply]
          rw [hmajorant, hcore, hcore]
        · cases n with
          | zero => exact Fin.elim0 i
          | succ n =>
              change
                S.majorant q.1 i.succ
                      (Fin.cons q.2.1 x) *
                    S.majorant q.1 i.succ
                      (Fin.cons q.2.2 x) =
                  T.majorant q.1 i.succ
                      (Fin.cons q.2.1 x) *
                    T.majorant q.1 i.succ
                      (Fin.cons q.2.2 x)
              rw [hmajorant, hmajorant]
