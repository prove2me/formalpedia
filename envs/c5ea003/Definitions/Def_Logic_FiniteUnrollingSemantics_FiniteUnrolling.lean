-- Prove2me | Definitions.Def_Logic_FiniteUnrollingSemantics_FiniteUnrolling
-- name    : Logic_FiniteUnrollingSemantics_FiniteUnrolling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:16.093629+00:00
-- url     : https://prove2.me/theorems/18458f07-bf80-4a2d-8230-b4b5734c0fc2
-- title:
--   Aether Catalog definitions — Logic_FiniteUnrollingSemantics_FiniteUnrolling
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.FiniteUnrollingSemantics.FiniteUnrolling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/FiniteUnrollingSemantics/FiniteUnrolling.lean by skeleton subtraction
import Mathlib

/-! # Finite Unrolling Semantics for Feedback Loops

This file provides the finite unrolling infrastructure for stateful
feedback loops, establishing that finite approximations faithfully
capture the semantics of guarded iteration.

## Main definitions

* `unrollChain` — the chain of finite unrollings of a feedback loop
* `unrollState` — extracting just the state component from an unrolling

## Main results

* `unrollChain_zero` — base case of unrolling
* `unrollChain_succ` — inductive step of unrolling
* `unrollState_eq_iterate` — the state component of unrolling n equals
  the n-th Kleene iterate of the feedback functional
-/

universe u

/-! ## Finite Unrolling Chain -/

/-- Finite unrolling of a stateful map at depth n. -/
def unrollChain
    {σ α β : Type u}
    (f : σ × α → σ × β) : ℕ → σ → α → σ × β
  | 0 => fun s a => (s, (f (s, a)).2)
  | n + 1 => fun s a =>
      let r := unrollChain f n s a
      f (r.1, a)

/-- The state component of an unrolling. -/
def unrollState
    {σ α β : Type u}
    (f : σ × α → σ × β) (n : ℕ) (s : σ) (a : α) : σ :=
  (unrollChain f n s a).1


/-! ## Basic Properties -/





/-! ## Equivalence with Iteration -/

/-- Two stateful maps are unrolling-equivalent if they produce the same
result at every finite depth, starting state, and input. -/
def UnrollingEquiv
    {σ α β : Type u}
    (f g : σ × α → σ × β) : Prop :=
  ∀ n s a, unrollChain f n s a = unrollChain g n s a





/-
Unrolling equivalence at depth 1 implies pointwise equality.
-/


