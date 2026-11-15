-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:42.518015+00:00
-- url     : https://prove2.me/theorems/9152fb8d-6b86-4ba0-a5d5-22b561df45e9
-- title:
--   Coordinate decompositions for projected majorant moments
-- statement:
--   For a distinguished coordinate $j$, the projection tuple selects the false endpoint at every other coordinate and replaces the endpoint at $j$ by the selected Boolean value $b$. The associated deleted-cube vertex makes exactly this choice for each face colour.
--
--   The doubled-cube equivalence splits a point into three pieces: the shared false endpoints outside $j$, the pair of endpoints at $j$, and the unused true endpoints outside $j$. Its inverse inserts the two distinguished endpoints into the respective false and true tuples. This is a concrete bijection of coordinate spaces over $\mathbb Z/N\mathbb Z$, with no positivity condition on $N$ required for the coordinate construction itself.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ProjectedMajorantExpansion.lean#L33-L400

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Lean
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection geometry -/

/-- The Boolean vertex used for colour `i` in the projected-majorant
expansion.  It chooses `b` at the eliminated coordinate `j` and the canonical
`false` copy at every other coordinate. -/
def apProjectionVertex
    {k : ℕ} (j i : Fin k) (b : Bool) :
    DeletedCube k i :=
  fun q => if q.1 = j then b else false

/-- The full one-copy simplex tuple selected from a doubled CFZ point:
start with all `false` coordinates and replace coordinate `j` by its `b`
copy. -/
def apProjectionTuple
    {k N : ℕ} (j : Fin k) (b : Bool)
    (x : CubePoint k N) :
    Fin k → ZMod N :=
  Function.update (fun i => x i false) j (x j b)



















/-! ## One-copy and two-copy selectors -/













/-! ## The finite coordinate equivalence -/

/-- Split a doubled CFZ point into:

* the shared `false` tuple on coordinates other than `j`;
* the `false` and `true` values at `j`;
* the unused `true` tuple on coordinates other than `j`.

This is the coordinate equivalence behind both projected moment identities.
-/
def apProjectionCubeEquiv
    (n N : ℕ) (j : Fin (n + 1)) :
    CubePoint (n + 1) N ≃
      (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
        (Fin n → ZMod N)) where
  toFun x :=
    (((fun t => x (j.succAbove t) false),
      (x j false, x j true)),
      fun t => x (j.succAbove t) true)
  invFun p i b :=
    match b with
    | false =>
        (Fin.insertNth j p.1.2.1 p.1.1 :
          Fin (n + 1) → ZMod N) i
    | true =>
        (Fin.insertNth j p.1.2.2 p.2 :
          Fin (n + 1) → ZMod N) i
  left_inv x := by
    funext i b
    cases b with
    | false =>
        change
          (Fin.insertNth j (x j false)
              (fun t => x (j.succAbove t) false) :
                Fin (n + 1) → ZMod N) i =
            x i false
        have htuple :
            Fin.insertNth j (x j false)
                (fun t => x (j.succAbove t) false) =
              fun q => x q false := by
          apply (Fin.insertNth_eq_iff).2
          exact ⟨rfl, rfl⟩
        exact congrFun htuple i
    | true =>
        change
          (Fin.insertNth j (x j true)
              (fun t => x (j.succAbove t) true) :
                Fin (n + 1) → ZMod N) i =
            x i true
        have htuple :
            Fin.insertNth j (x j true)
                (fun t => x (j.succAbove t) true) =
              fun q => x q true := by
          apply (Fin.insertNth_eq_iff).2
          exact ⟨rfl, rfl⟩
        exact congrFun htuple i
  right_inv p := by
    rcases p with ⟨⟨y, ⟨a₀, a₁⟩⟩, y₁⟩
    apply Prod.ext
    · apply Prod.ext
      · funext t
        simp
      · apply Prod.ext <;> simp
    · funext t
      simp

/-! ## Exact projected moment identities -/





/-! ## Linear forms imply projected-majorant moments -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apProjectionCubeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apProjectionCubeEquiv.match_1,
    `Wikipedia.SzemeredisTheorem.apProjectionTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.apProjectionVertex.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


