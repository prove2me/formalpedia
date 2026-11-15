-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:55:23.395304+00:00
-- url     : https://prove2.me/submissions/6a21fc15-5603-45aa-bf8b-6a1919a90f2c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_linearFormsProduct_maskedOneCopy_eq_incidentMajorantProduct

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)





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

/-- A normalized average over a product is the corresponding iterated
normalized average. -/
theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

/-- Averaging a function that ignores a nonempty product coordinate does
not change its normalized average. -/
theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]



end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Majorants with previously densified colours set to one -/
/-! ## Masked CFZ selectors -/
/-! ## Exact mixed projected moments -/

open Wikipedia.SzemeredisTheorem in
/-- The first moment of a mixed projected majorant is an explicit
one-copy subproduct of the original CFZ system. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    mean (apMaskedProjectedMajorant n N ν active j) =
      mean (linearFormsProduct (n + 1) N ν
        (apMaskedProjectedOneCopyExponent n active j)) := by
  change
    mean (fun y : Fin n → ZMod N =>
      mean (fun a : ZMod N =>
        apMaskedIncidentMajorantProduct n N ν active j a y)) = _
  calc
    mean (fun y : Fin n → ZMod N =>
        mean (fun a : ZMod N =>
          apMaskedIncidentMajorantProduct n N ν active j a y)) =
        mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a y) :=
      rfl
    _ = mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N × ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a.1 y) := by
      unfold mean₂
      apply congrArg mean
      funext y
      exact
        (mean_prod_fst
          (fun a : ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a y)).symm
    _ = mean (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
        apMaskedIncidentMajorantProduct n N ν active j q.2.1 q.1) :=
      (mean_prod_type _).symm
    _ = mean (fun p :
          (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
            (Fin n → ZMod N)) =>
        apMaskedIncidentMajorantProduct n N ν active j
          p.1.2.1 p.1.1) :=
      (mean_prod_fst
        (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
          apMaskedIncidentMajorantProduct n N ν active j
            q.2.1 q.1)).symm
    _ = mean (linearFormsProduct (n + 1) N ν
          (apMaskedProjectedOneCopyExponent n active j)) := by
      symm
      apply mean_equiv (apProjectionCubeEquiv n N j)
      intro x
      simpa [apProjectionCubeEquiv] using
        linearFormsProduct_maskedOneCopy_eq_incidentMajorantProduct
          n N ν active j x
