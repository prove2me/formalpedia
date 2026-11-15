-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:01:46.06549+00:00
-- url     : https://prove2.me/submissions/22cb789b-39bb-4bc7-8c20-cd27050495fd

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_abs_form_pow_two_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_hasRecursiveBounds_of_hasCFZCertificate
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_heterogeneousMaskSimplexMajorizedCutSystem_hasCFZCertificate

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
# Elementary properties of the linear-forms condition

This file records the normalization and positivity facts that every later
transference estimate uses.  The deep input—that the W-tricked Selberg
majorant satisfies this condition—is isolated in the sieve layer.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem linearFormsProduct_empty (k N : ℕ) (ν : ZMod N → ℝ)
    (x : CubePoint k N) :
    linearFormsProduct k N ν (emptyLinearFormsExponent k) x = 1 := by
  simp [linearFormsProduct, emptyLinearFormsExponent]





/-- Testing the empty subproduct forces the error tolerance to be
nonnegative. -/
theorem HasLinearFormsCondition.error_nonneg {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η) :
    0 ≤ η := by
  have he := h (emptyLinearFormsExponent k)
  have hproduct :
      linearFormsProduct k N ν (emptyLinearFormsExponent k) =
        fun _ => 1 := by
    funext x
    exact linearFormsProduct_empty k N ν x
  rw [hproduct] at he
  simpa using he





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
# Repeated weighted Cauchy--Schwarz for strong linear forms

This file supplies the recursive analytic bridge which precedes the
algebraic endpoint in `WeightedStrongLinearForms`.

The recursion is the quantitative finite version of Conlon--Fox--Zhao,
Lemma 6.3.  A parameterized cut system consists of a possibly signed core
and one nonnegative factor for every deleted coordinate.  Each factor is
dominated by a designated majorant.  One Cauchy--Schwarz step

* removes the head factor;
* pays the normalized mean of its majorant;
* duplicates the head coordinate;
* pairs every remaining factor; and
* inserts the removed majorant into the new core.

After all coordinates have been processed, the core is the product of all
copies of the original centered factor together with exactly one copy of
each selected face majorant.  No pointwise bound on the majorants is used.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Weighted finite Cauchy--Schwarz -/









/-! ## Parameterized majorized cut systems -/



namespace MajorizedCutSystem

variable {P G : Type*} {n : ℕ}



















/-! ## Quantitative iteration -/









end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/



namespace MajorizedCutSystem



















/-- Quantitative weighted strong-linear-forms Cauchy--Schwarz bridge.

For a system with `n` remaining coordinates, arbitrary nonnegative cut
factors may be used as long as they are dominated by the certified
majorants.  Repeated Cauchy--Schwarz then costs
`(1 + η)^(2^n - 1)` and terminates at the exact weighted endpoint already
proved in `WeightedStrongLinearForms`. -/
theorem abs_form_pow_two_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S) :
    |S.form| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) := by
  exact abs_form_pow_two_le
    (B := 1 + η)
    (E := (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
    (by linarith [hLF.error_nonneg])
    S
    (hasRecursiveBounds_of_hasCFZCertificate hLF j S hS)

/-- Root-extracted form of the weighted strong-linear-forms estimate.

This is the interface used by relative counting: it keeps the analytic
parameter conversion separate from the Cauchy--Schwarz recursion. -/
theorem abs_form_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ n - 1) *
          ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) ≤
        ε ^ (2 ^ n)) :
    |S.form| ≤ ε := by
  exact le_of_pow_le_pow_left₀
    (pow_ne_zero _ two_ne_zero) hε
    ((abs_form_pow_two_le_of_hasCFZCertificate hLF j S hS).trans hconvert)





end MajorizedCutSystem

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





@[simp]
theorem apFalseSparseTrueDenseMask_false
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseSparseTrueDenseMask active false i =
      active i := by
  rfl

@[simp]
theorem apFalseSparseTrueDenseMask_true
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseSparseTrueDenseMask active true i =
      false := by
  rfl











/-! ## Arbitrary weighted-simplex factors -/

namespace MajorizedCutSystem



end MajorizedCutSystem



theorem heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    heterogeneousMaskSimplexTwoCopyCutTest
        n N H j a t (eraseCoordinate t y) =
      ∏ b : Bool,
        (H b).edgeWeight (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j (a b) y)
            (j.succAbove t)) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold heterogeneousMaskSimplexTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]

theorem prod_heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ t : Fin n,
        heterogeneousMaskSimplexTwoCopyCutTest
          n N H j a t (eraseCoordinate t y)) =
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y := by
  simp_rw [
    heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate]
  unfold generalSimplexIncidentProduct
  rw [Finset.prod_comm]









theorem heterogeneousMaskSimplexMajorizedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
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
    (heterogeneousMaskSimplexMajorizedCutSystem
        n N ν active H j hrest).form =
      heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        n N ν H j := by
  unfold MajorizedCutSystem.form
  unfold heterogeneousMaskSimplexMajorizedCutSystem
  unfold heterogeneousMaskSimplexTwoCopyCenteredCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  change
    apFaceCenteredCore n N ν j y *
        ∏ t : Fin n,
          heterogeneousMaskSimplexTwoCopyCutTest
            n N H j a t (eraseCoordinate t y) =
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct
            (H b) j (a b) y
  rw [
    prod_heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate]

namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary-factor quantitative bridge -/

/-- Quantitative CFZ root bound for arbitrary weighted-simplex factors
under independent masks on the two Boolean copies. -/
theorem HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Bool → Fin (m + 2) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν H j| ≤ ε := by
  rw [← heterogeneousMaskSimplexMajorizedCutSystem_form
    (m + 1) N ν active H j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (heterogeneousMaskSimplexMajorizedCutSystem
        (m + 1) N ν active H j hrest)
      (MajorizedCutSystem.heterogeneousMaskSimplexMajorizedCutSystem_hasCFZCertificate
        (m + 1) N ν hν active H j hrest)
      hε hconvert



@[simp]
theorem heterogeneousMaskSimplexCopyPair_false
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    heterogeneousMaskSimplexCopyPair H K false = H := by
  rfl

@[simp]
theorem heterogeneousMaskSimplexCopyPair_true
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    heterogeneousMaskSimplexCopyPair H K true = K := by
  rfl

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
/-! ## Arbitrary-factor quantitative bridge -/
open Wikipedia.SzemeredisTheorem.HasLinearFormsCondition

open Wikipedia.SzemeredisTheorem.HasLinearFormsCondition in
/-- One orientation of the mixed-copy estimate: the `false` copy is below
the active AP mask, and the `true` copy lies in the unit interval. -/
theorem solution
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      ∀ i x,
        0 ≤ H.edgeWeight i x ∧
          H.edgeWeight i x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight i x)
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair H K) j| ≤ ε := by
  apply
    hLF.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le
      hν (apFalseSparseTrueDenseMask active)
      (heterogeneousMaskSimplexCopyPair H K) j
      (hrest := ?_) hε hconvert
  intro b t x
  cases b with
  | false =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hH (j.succAbove t) x
  | true =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hK (j.succAbove t) x
