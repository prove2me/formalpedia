-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:57:50.065709+00:00
-- url     : https://prove2.me/theorems/ae1fadf6-b597-4de1-99c3-2e7e6d4feb15
-- title:
--   Selectors, centered products, and coordinate scalings on one CFZ face
-- statement:
--   At a fixed face $j$ of the CFZ system, a Boolean selector is extended by false to all other faces. The corresponding factor family is $\nu(\psi_{j,\omega}(x))$, and the centered face product is
--
--   $$
--   \prod_{\omega}\bigl(\nu(\psi_{j,\omega}(x))-1\bigr).
--   $$
--
--   The bundle provides the canonical reindexing of the deleted Boolean cube by $\operatorname{Fin}(n)$ when the full coordinate set is $\operatorname{Fin}(n+1)$. It also supplies the equivalence that applies a chosen additive automorphism to both Boolean endpoints of each coordinate. These transformations keep the face and endpoint indexing explicit in the moment calculations.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L20-L221

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
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
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Reindex a deleted Boolean cube by the canonical `Fin n` enumeration of
the coordinates other than `j`. -/
noncomputable def deletedCubeEquiv
    {n : ℕ} (j : Fin (n + 1)) :
    (Fin n → Bool) ≃ DeletedCube (n + 1) j :=
  Equiv.arrowCongr (finSuccAboveEquiv j) (Equiv.refl Bool)



/-- Extend a Boolean selector on the forms belonging to the face `j` by
`false` on every other face. -/
def faceLinearFormsExponent {k : ℕ} (j : Fin k)
    (e : BooleanCube (DeletedCube k j)) :
    LinearFormsExponent k :=
  fun j' ω =>
    if h : j' = j then e (h ▸ ω) else false



/-- The family of majorant factors on one fixed CFZ face. -/
def faceFactorFamily (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) :
    DeletedCube k j → CubePoint k N → ℝ :=
  fun ω x => ν (apLinearForm k N j ω x)





/-- The centered product over all forms on one face. -/
def faceCenteredProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) (x : CubePoint k N) : ℝ :=
  ∏ ω : DeletedCube k j,
    (ν (apLinearForm k N j ω x) - 1)









/-- Apply one additive automorphism to both endpoints in every
coordinate. -/
def endpointScalingEquiv
    {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : Fin n → G ≃+ G) :
    (Fin n → Bool → G) ≃ (Fin n → Bool → G) where
  toFun x i b := e i (x i b)
  invFun x i b := (e i).symm (x i b)
  left_inv x := by
    funext i b
    exact (e i).symm_apply_apply (x i b)
  right_inv x := by
    funext i b
    exact (e i).apply_symm_apply (x i b)















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.deletedCubeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.faceFactorFamily.eq_1,
    `Wikipedia.SzemeredisTheorem.faceLinearFormsExponent.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


