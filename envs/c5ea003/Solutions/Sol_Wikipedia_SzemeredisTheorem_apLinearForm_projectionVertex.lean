-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apLinearForm_projectionVertex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:23:57.829697+00:00
-- url     : https://prove2.me/submissions/148d94ce-f216-4f0d-b110-5b3a6c490a52

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Projection geometry -/

open Wikipedia.SzemeredisTheorem in
/-- A selected CFZ form is exactly the corresponding AP-simplex form on
the full tuple chosen by `apProjectionTuple`. -/
theorem solution
    {k N : ℕ} (j i : Fin k)
    (b : Bool) (x : CubePoint k N) :
    apLinearForm k N i (apProjectionVertex j i b) x =
      apSimplexForm k N i
        (deleteCoordinate (apProjectionTuple j b x) i) := by
  unfold apLinearForm apSimplexForm
  apply Fintype.sum_congr
  intro q
  apply congrArg (fun z : ZMod N =>
    ((((q.1 : ℤ) - (i : ℤ) : ℤ) : ZMod N) * z))
  change
    x q.1 (if q.1 = j then b else false) =
      Function.update (fun r => x r false) j (x j b) q.1
  by_cases hq : q.1 = j
  · subst j
    simp
  · simp [hq]
