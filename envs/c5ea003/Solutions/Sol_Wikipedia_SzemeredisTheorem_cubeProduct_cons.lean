-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cubeProduct_cons
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:40.809396+00:00
-- url     : https://prove2.me/submissions/fcfee309-cfad-41d0-98b5-0965a5ffc37d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



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











@[simp]
theorem cubeVertex_cons
    {G : Type*} {n : ℕ}
    (p : G × G) (x : Fin n → G × G)
    (b : Bool) (ω : Fin n → Bool) :
    cubeVertex (Fin.cons p x) (Fin.cons b ω) =
      Fin.cons (selectPair p b) (cubeVertex x ω) := by
  funext i
  cases i using Fin.cases <;> simp [cubeVertex]

























































end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Splitting the head cube coordinate pairs the two head-coordinate copies
of `F` at every remaining cube vertex. -/
theorem solution
    {G : Type*} {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (p : G × G) (x : Fin n → G × G) :
    (∏ ω : Fin (n + 1) → Bool,
        F (cubeVertex (Fin.cons p x) ω)) =
      ∏ ω : Fin n → Bool,
        pairedTupleFunction F p (cubeVertex x ω) := by
  calc
    (∏ ω : Fin (n + 1) → Bool,
        F (cubeVertex (Fin.cons p x) ω)) =
        ∏ q : Bool × (Fin n → Bool),
          F (cubeVertex (Fin.cons p x)
            (Fin.cons q.1 q.2)) := by
      apply Fintype.prod_equiv
        (Fin.consEquiv
          (fun _ : Fin (n + 1) => Bool)).symm
      intro ω
      simp
    _ = ∏ ω : Fin n → Bool, ∏ b : Bool,
          F (cubeVertex (Fin.cons p x)
            (Fin.cons b ω)) :=
      Fintype.prod_prod_type_right _
    _ = ∏ ω : Fin n → Bool,
          pairedTupleFunction F p (cubeVertex x ω) := by
      apply Finset.prod_congr rfl
      intro ω _
      simp [pairedTupleFunction, mul_comm]
