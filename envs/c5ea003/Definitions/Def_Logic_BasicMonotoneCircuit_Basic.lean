-- Prove2me | Definitions.Def_Logic_BasicMonotoneCircuit_Basic
-- name    : Logic_BasicMonotoneCircuit_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:48:45.553499+00:00
-- url     : https://prove2.me/theorems/f1c9abe5-f1a4-49a9-90ce-6a30567baba9
-- title:
--   Aether Catalog definitions — Logic_BasicMonotoneCircuit_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.BasicMonotoneCircuit.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/BasicMonotoneCircuit/Basic.lean by skeleton subtraction
import Mathlib

/-! # Basic monotone circuit complexity -/

namespace CircuitComplexity

/-- Monotone Boolean circuits with variables, constants, conjunction, and disjunction. -/
inductive MCircuit (ι : Type*) where
  | var (i : ι)
  | top
  | bot
  | and (left right : MCircuit ι)
  | or (left right : MCircuit ι)

namespace MCircuit

variable {ι : Type*}

/-- Evaluation of a monotone circuit. -/
def eval : MCircuit ι → (ι → Bool) → Bool
  | var i, x => x i
  | top, _ => true
  | bot, _ => false
  | and a b, x => a.eval x && b.eval x
  | or a b, x => a.eval x || b.eval x

/-- Circuit size, counting every node. -/
def size : MCircuit ι → ℕ
  | var _ => 1
  | top => 1
  | bot => 1
  | and a b => a.size + b.size + 1
  | or a b => a.size + b.size + 1


/-- A Boolean function depends on a variable if flipping that variable can change its value. -/
def DependsOn [DecidableEq ι] (f : (ι → Bool) → Bool) (i : ι) : Prop :=
  ∃ x, f (Function.update x i false) ≠ f (Function.update x i true)

/-- The finite set of variables occurring in a circuit. -/
def vars [DecidableEq ι] : MCircuit ι → Finset ι
  | var i => {i}
  | top => ∅
  | bot => ∅
  | and a b => a.vars ∪ b.vars
  | or a b => a.vars ∪ b.vars





end MCircuit
end CircuitComplexity


