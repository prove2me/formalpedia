-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:30.308679+00:00
-- url     : https://prove2.me/theorems/72d6d5ca-6e23-49f5-a379-f35d5fed0fc8
-- title:
--   Recursive box moments and coordinate cut forms
-- statement:
--   A pair of endpoints in each coordinate determines one cube vertex for each Boolean selector. For a real function $F$ on $n$ coordinates over a finite type, the explicit cube moment is the normalized mean of the product of $F$ over all $2^n$ vertices. The recursive box moment duplicates the first coordinate at each successor step and averages the resulting product; a Boolean-endpoint presentation is supplied as well.
--
--   The coordinate cut form averages $F(x)$ times one factor depending on each deleted-coordinate tuple. Absolute boundedness requires each such factor to have absolute value at most one. The paired-tail and tail-integrand constructions record the factors remaining after separating the first coordinate in Cauchy–Schwarz. Endpoint selection and its elementary certificates keep the two-coordinate encodings compatible.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L21-L283

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
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
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Pair a function on `(n + 1)` coordinates at two values of its first
coordinate. -/
def pairedTupleFunction {G : Type*} {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) (p : G × G) :
    (Fin n → G) → ℝ :=
  fun y => F (Fin.cons p.1 y) * F (Fin.cons p.2 y)

/-- Select the first component at `false` and the second at `true`. -/
def selectPair {G : Type*} (p : G × G) : Bool → G
  | false => p.1
  | true => p.2

@[simp]
theorem selectPair_false {G : Type*} (p : G × G) :
    selectPair p false = p.1 :=
  rfl

@[simp]
theorem selectPair_true {G : Type*} (p : G × G) :
    selectPair p true = p.2 :=
  rfl

/-- Vertex of a cube whose `i`-th pair of endpoints is `x i`. -/
def cubeVertex {G : Type*} {n : ℕ}
    (x : Fin n → G × G) (ω : Fin n → Bool) : Fin n → G :=
  fun i => selectPair (x i) (ω i)



/-- The recursive box moment.  At each successor step the first coordinate
is duplicated and the two resulting copies of the function are multiplied.
-/
noncomputable def boxMoment {G : Type*} [Fintype G] :
    (n : ℕ) → ((Fin n → G) → ℝ) → ℝ
  | 0, F => mean F
  | n + 1, F =>
      mean fun p : G × G =>
        boxMoment n (pairedTupleFunction F p)





/-- Explicit cube-vertex form of the box moment. -/
noncomputable def cubeMean {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) : ℝ :=
  mean fun x : Fin n → G × G =>
    ∏ ω : Fin n → Bool, F (cubeVertex x ω)

/-- Package two Boolean-indexed endpoints as a pair, independently in every
coordinate. -/
def endpointTupleEquiv {G : Type*} {n : ℕ} :
    (Fin n → Bool → G) ≃ (Fin n → G × G) where
  toFun x i := (x i false, x i true)
  invFun x i := selectPair (x i)
  left_inv x := by
    funext i b
    cases b <;> rfl
  right_inv x := by
    funext i
    exact Prod.ext rfl rfl





/-- Cube moment with the two endpoints represented as a Boolean-indexed
function rather than a pair. -/
noncomputable def cubeFunctionMean
    {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) : ℝ :=
  mean fun x : Fin n → Bool → G =>
    ∏ ω : Fin n → Bool, F (fun i => x i (ω i))









/-- A coordinate cut form for an arbitrary function on a finite product. -/
noncomputable def coordinateCutForm
    {G : Type*} [Fintype G] (n : ℕ)
    (F : (Fin n → G) → ℝ) (u : CutTestFamily G n) : ℝ :=
  mean fun x => F x * ∏ i, u i (eraseCoordinate i x)

/-- Absolute boundedness is the natural hypothesis for the Cauchy--Schwarz
argument; unlike cut discrepancy, signs of the coordinate factors do not
matter. -/
def IsAbsBoundedCutTest {G : Type*} {n : ℕ}
    (u : CutTestFamily G n) : Prop :=
  ∀ i x, |u i x| ≤ 1







/-- After duplicating the head coordinate, pair every remaining deleted
coordinate factor.  The `n = 0` branch is vacuous. -/
def pairedTailCut
    {G : Type*} :
    {n : ℕ} →
      CutTestFamily G (n + 1) → G × G → CutTestFamily G n
  | 0, _, _ => fun i _ => Fin.elim0 i
  | _ + 1, u, p => fun i z =>
      u i.succ (Fin.cons p.1 z) *
        u i.succ (Fin.cons p.2 z)



/-- The part of a successor-dimensional cut form left after its head
coordinate factor has been pulled outside the head-coordinate mean. -/
noncomputable def tailCutIntegrand
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (y : Fin n → G) (a : G) : ℝ :=
  F (Fin.cons a y) *
    ∏ i : Fin n,
      u i.succ
        (eraseCoordinate i.succ (Fin.cons a y))

















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.boxMoment.match_1,
    `Wikipedia.SzemeredisTheorem.coordinateCutForm.eq_1,
    `Wikipedia.SzemeredisTheorem.cubeVertex.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedTailCut.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedTailCut.eq_2,
    `Wikipedia.SzemeredisTheorem.pairedTailCut.match_1,
    `Wikipedia.SzemeredisTheorem.pairedTupleFunction.eq_1,
    `Wikipedia.SzemeredisTheorem.selectPair.match_1,
    `Wikipedia.SzemeredisTheorem.tailCutIntegrand.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


