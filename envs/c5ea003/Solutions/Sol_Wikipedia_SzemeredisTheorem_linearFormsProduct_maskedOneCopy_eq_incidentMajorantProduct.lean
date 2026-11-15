-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.linearFormsProduct_maskedOneCopy_eq_incidentMajorantProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:54:18.692304+00:00
-- url     : https://prove2.me/submissions/1043246f-098f-44b0-a8da-e2584f451023

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apLinearForm_projectionVertex

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# The AP-simplex projected majorant

Fix a colour `j` of the canonical `(n + 1)`-colour arithmetic-progression
simplex.  A point of the distinguished `j`-edge is written canonically as
`y : Fin n → ZMod N`.  Inserting `a : ZMod N` at coordinate `j` produces a
full simplex point.  The projected majorant is

```
ν'_j(y) = 𝔼 a, ∏ t, ν(L_{j.succAbove t}(insertNth j a y)),
```

the conditional average of all incident majorant edges other than colour
`j`.

Its square uses two independent values of the eliminated coordinate while
sharing `y`.  These are exactly the one-copy and two-copy subproducts of the
CFZ linear-forms system which choose respectively the `false` vertex and the
`false`/`true` vertices at coordinate `j`, keeping every other doubled
coordinate at `false`.  The unused `true` copies of the coordinates in `y`
are removed by an explicit finite coordinate equivalence below.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection geometry -/







/-- In canonical deleted-face coordinates, `apProjectionTuple` is
literally insertion of the eliminated coordinate. -/
theorem apProjectionTuple_eq_insertNth
    {n N : ℕ} (j : Fin (n + 1)) (b : Bool)
    (x : CubePoint (n + 1) N) :
    apProjectionTuple j b x =
      Fin.insertNth j (x j b)
        (fun t => x (j.succAbove t) false) := by
  apply (Fin.eq_insertNth_iff).2
  constructor
  · simp [apProjectionTuple]
  · funext t
    rw [Fin.removeNth_apply]
    simp [apProjectionTuple]















/-! ## One-copy and two-copy selectors -/













/-! ## The finite coordinate equivalence -/



/-! ## Exact projected moment identities -/





/-! ## Linear forms imply projected-majorant moments -/



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

open Wikipedia.SzemeredisTheorem in
/-- The masked one-copy CFZ subproduct is exactly the active incident
majorant product. -/
theorem solution
    (n N : ℕ) (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apMaskedProjectedOneCopyExponent n active j) x =
      apMaskedIncidentMajorantProduct n N ν active j
        (x j false)
        (fun t => x (j.succAbove t) false) := by
  classical
  unfold apMaskedIncidentMajorantProduct
  unfold apHeterogeneousIncidentProduct
  rw [linearFormsProduct, Fin.prod_univ_succAbove _ j]
  have hself :
      (∏ ω : DeletedCube (n + 1) j,
        if apMaskedProjectedOneCopyExponent n active j j ω then
          ν (apLinearForm (n + 1) N j ω x)
        else 1) = 1 := by
    apply Fintype.prod_eq_one
    intro ω
    simp [apMaskedProjectedOneCopyExponent]
  rw [hself, one_mul]
  apply Fintype.prod_congr
  intro t
  cases hactive : active (j.succAbove t) with
  | false =>
      simp [apMaskedProjectedOneCopyExponent,
        apMaskedFaceMajorant, hactive, Fin.succAbove_ne]
  | true =>
      let v :=
        apProjectionVertex j (j.succAbove t) false
      rw [Fintype.prod_eq_single v]
      · have hform :=
          congrArg ν
            (apLinearForm_projectionVertex
              j (j.succAbove t) false x)
        simpa [apMaskedProjectedOneCopyExponent,
          apMaskedFaceMajorant, hactive, v, Fin.succAbove_ne,
          apProjectionTuple_eq_insertNth] using hform
      · intro ω hω
        simp [apMaskedProjectedOneCopyExponent,
          hactive, v, Fin.succAbove_ne, hω]
