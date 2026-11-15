-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.terminalFaceMajorantProduct_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:49.025202+00:00
-- url     : https://prove2.me/submissions/e0996d86-b228-40a4-ac88-d2c06c6c08c5

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexForm_eq_apLinearForm_terminalFaceVertex

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
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x

/-- Replacing coordinate `t` before inserting the distinguished coordinate
`j` only replaces coordinate `j.succAbove t` of the resulting full tuple. -/
theorem insertNth_insertNth_eraseCoordinate
    {n : ℕ} {G : Type*}
    (j : Fin (n + 2)) (t : Fin (n + 1))
    (a b : G) (y : Fin (n + 1) → G) :
    Fin.insertNth j a
        (Fin.insertNth t b (eraseCoordinate t y)) =
      (Function.update (Fin.insertNth j a y)
        (j.succAbove t) b : Fin (n + 2) → G) := by
  rw [insertNth_eraseCoordinate_eq_update, Fin.insertNth_update]

























end Wikipedia.SzemeredisTheorem

end

section


/-!
# Mixed projected moments for recursive relative densification

After one colour has been densified, its majorant is the constant function
one.  At the next stage the projected majorant is therefore not the product
of a common `ν` on every incident colour: it is a mixed product, with `ν`
only on the colours which remain sparse and `1` on the colours already
densified.

This file closes that moment gap.  A Boolean mask records the remaining
sparse colours.  We expand the first and second moments of the corresponding
projected majorant as explicit subproducts of the original CFZ linear-forms
system.  Consequently one unchanged `HasLinearFormsCondition` supplies the
moment package for every recursive mask, and hence supplies the next
heterogeneous full-to-projected state transition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Majorants with previously densified colours set to one -/



@[simp]
theorem apMaskedFaceMajorant_of_active
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = true) :
    apMaskedFaceMajorant ν active i z = ν z := by
  simp [apMaskedFaceMajorant, hi]

@[simp]
theorem apMaskedFaceMajorant_of_inactive
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = false) :
    apMaskedFaceMajorant ν active i z = 1 := by
  simp [apMaskedFaceMajorant, hi]







/-! ## Masked CFZ selectors -/









/-! ## Exact mixed projected moments -/





/-! ## The recursive moment and state-transition certificates -/





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











end MajorizedCutSystem

/-! ## The centered AP face as a box core -/





namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## Concrete two-copy AP cut factors -/



/-- Evaluating a reconstructed factor on an erased shared tuple recovers
the two actual incident AP faces. -/
theorem apTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    apTwoCopyCutTest n N g j a t
        (eraseCoordinate t y) =
      ∏ b : Bool,
        g b (j.succAbove t)
          (apSimplexForm (n + 1) N (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b) y)
              (j.succAbove t))) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold apTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]









/-! ## A single paid active face -/

















/-! ## Mixed active-majorant system -/













/-! ## The bounded two-copy certificate -/













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

open Wikipedia.SzemeredisTheorem in
/-- A fully doubled reconstructed majorant on one non-distinguished face
is exactly the full CFZ face product when that face is active, and one
when it is inactive. -/
theorem solution
    (m N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin ((m + 1) + 1) → Bool)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (p : Bool → ZMod N)
    (a : Fin (m + 1) → ZMod N × ZMod N) :
    (∏ bits : Fin m → Bool,
      apTwoCopyCutTest (m + 1) N
        (fun _ => apMaskedFaceMajorant ν active)
        j p t
        (eraseCoordinate t
          (fun q =>
            selectPair (a q)
              (@Fin.insertNth m
                (fun _ => Bool) t false bits q)))) =
      ∏ ω :
          DeletedCube ((m + 1) + 1)
            (j.succAbove t),
        if active (j.succAbove t) then
          ν (apLinearForm ((m + 1) + 1) N
            (j.succAbove t) ω
            (apCSTerminalCubeEquiv
              (m + 1) N j (p, a)))
        else 1 := by
  classical
  simp_rw [apTwoCopyCutTest_eraseCoordinate]
  cases hactive : active (j.succAbove t) with
  | false =>
      simp_rw [apMaskedFaceMajorant_of_inactive
        ν active (j.succAbove t) _ hactive]
      simp
  | true =>
      simp_rw [apMaskedFaceMajorant_of_active
        ν active (j.succAbove t) _ hactive]
      simp only [if_true]
      let F :
          Bool → (Fin m → Bool) → ℝ :=
        fun b bits =>
          ν (apSimplexForm ((m + 1) + 1) N
            (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (p b)
                (fun q =>
                  selectPair (a q)
                    (@Fin.insertNth m
                      (fun _ => Bool) t false bits q)))
              (j.succAbove t)))
      change
        (∏ bits : Fin m → Bool,
          ∏ b : Bool, F b bits) = _
      rw [Finset.prod_comm]
      rw [← Fintype.prod_prod_type
        (fun q : Bool × (Fin m → Bool) =>
          F q.1 q.2)]
      apply Fintype.prod_equiv
        (apCSTerminalFaceVertexEquiv m j t)
      intro bits
      unfold F
      apply congrArg ν
      exact
        apSimplexForm_eq_apLinearForm_terminalFaceVertex
          m N j t p a bits.1 bits.2
