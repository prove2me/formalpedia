-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.iterNextTerminal_apTwoCopyMasked_form_of_fintype
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:54:46.704289+00:00
-- url     : https://prove2.me/submissions/ffc5665f-f00d-4e3a-aff1-3755ff956683

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_iterNextTerminalDecoded_core
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_terminalCoreProduct_apTwoCopyMasked
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_terminalMajorantProduct_apTwoCopyMasked

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









/-- Reindexing the finite external parameter does not change the represented
normalized cut form. -/
theorem reindex_form
    {P Q G : Type u}
    [Fintype P] [Fintype Q] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) :
    (S.reindex e).form = S.form := by
  unfold form mean₂ reindex
  apply mean_equiv e
  intro q
  rfl

























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











































end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/



















namespace MajorizedCutSystem





/-- Pointwise terminal identity for the decoded concrete mixed system. -/
theorem iterNextTerminalDecoded_apTwoCopyMasked_core
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    (iterNextTerminalDecoded
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest)).core
        (p, a) (fun i => Fin.elim0 i) =
      faceCenteredProduct (n + 1) N ν j
          (apCSTerminalCubeEquiv n N j (p, a)) *
        linearFormsProduct (n + 1) N ν
          (apCSActiveTerminalExponent active j)
          (apCSTerminalCubeEquiv
            n N j (p, a)) := by
  rw [iterNextTerminalDecoded_core]
  rw [terminalCoreProduct_apTwoCopyMasked,
    terminalMajorantProduct_apTwoCopyMasked]
  ring



















end MajorizedCutSystem

/-! ## Quantitative active-mask endpoint -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## The terminal AP cube and its face vertices -/
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- The complete terminal form is the weighted centered distinguished face
times precisely the active non-distinguished CFZ selector.  The statement
is uniform in the `Fintype` presentation of the nested parameter, which is
needed when it is reached through the actual recursive certificate. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (stageFintype :
      Fintype
        (CSStageParam
          (Bool → ZMod N) (ZMod N) n)) :
    @form
        (CSStageParam
          (Bool → ZMod N) (ZMod N) n)
        (ZMod N) 0 stageFintype
        (inferInstance : Fintype (ZMod N))
        (iterNextTerminal n
          (apTwoCopyMaskedMajorizedCutSystem
            n N ν active g j hrest)) =
      mean (fun x =>
        faceCenteredProduct (n + 1) N ν j x *
          linearFormsProduct (n + 1) N ν
            (apCSActiveTerminalExponent active j) x) := by
  let : Fintype
      (CSStageParam
        (Bool → ZMod N) (ZMod N) n) :=
    stageFintype
  rw [← reindex_form
    (iterNextTerminal n
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest))
    (csStageParamEquiv
      (Bool → ZMod N) (ZMod N) n).symm]
  unfold form mean₂
  simp only [Finset.univ_eq_empty,
    Finset.prod_empty, mul_one]
  apply mean_equiv
    (apCSTerminalCubeEquiv n N j)
  intro p
  change
    mean (fun x : Fin 0 → ZMod N =>
      (iterNextTerminalDecoded
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) = _
  rw [show
    (fun x : Fin 0 → ZMod N =>
      (iterNextTerminalDecoded
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) =
      fun _ =>
        (iterNextTerminalDecoded
          (apTwoCopyMaskedMajorizedCutSystem
            n N ν active g j hrest)).core
          p (fun i => Fin.elim0 i) by
      funext x
      apply congrArg
      funext i
      exact Fin.elim0 i]
  rw [mean_const]
  exact
    iterNextTerminalDecoded_apTwoCopyMasked_core
      n N ν active g j hrest p.1 p.2
