-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:39.943426+00:00
-- url     : https://prove2.me/theorems/8a75034b-4d3f-4450-9a3c-059150ebc623
-- title:
--   Transporting cut tests through coordinate automorphisms
-- statement:
--   Multiplication by a unit in a commutative ring is viewed as an additive automorphism. A family of additive automorphisms acts independently on all coordinates, with its inverse acting coordinatewise as well.
--
--   The pullback of a deleted-coordinate cut test applies the inverse automorphism at each remaining coordinate. The associated linear cut correlation replaces the ordinary coordinate sum by the sum of the automorphically transformed coordinates. These definitions retain the same deleted-coordinate test structure while allowing the coefficient automorphisms used by AP forms.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutTransport.lean#L16-L99

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Multiplication by a unit, regarded only as an additive automorphism. -/
noncomputable def mulAddEquivOfIsUnit
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a) :
    R ≃+ R :=
  DistribMulAction.toAddEquiv R ha.unit



/-- Apply an additive automorphism independently in every coordinate. -/
def coordinatewiseAddEquiv
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G) :
    (ι → G) ≃ (ι → G) where
  toFun x i := e i (x i)
  invFun x i := (e i).symm (x i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (e i).apply_symm_apply (x i)





/-- Pull a deleted-coordinate test through independent coordinate
automorphisms. -/
def pullCutTest
    {G : Type*} [AddCommGroup G] {r : ℕ}
    (e : Fin r → G ≃+ G) (u : CutTestFamily G r) :
    CutTestFamily G r := by
  cases r with
  | zero =>
      exact fun i => Fin.elim0 i
  | succ n =>
      exact fun i y =>
        u i (fun t => (e (i.succAbove t)).symm (y t))



/-- Cut correlation with an automorphic linear form in place of the literal
coordinate sum. -/
noncomputable def linearCutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, e i (x i)) -
        g (∑ i, e i (x i))) *
      ∏ i, u i (eraseCoordinate i x)





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.linearCutCorrelation.eq_1,
    `Wikipedia.SzemeredisTheorem.pullCutTest.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


