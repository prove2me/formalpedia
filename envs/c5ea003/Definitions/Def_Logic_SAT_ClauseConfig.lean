-- Prove2me | Definitions.Def_Logic_SAT_ClauseConfig
-- name    : Logic_SAT_ClauseConfig
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:37.321951+00:00
-- url     : https://prove2.me/theorems/9df4684e-18ba-464c-a796-4e272a7d96b4
-- title:
--   Aether Catalog definitions — Logic_SAT_ClauseConfig
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.SAT.ClauseConfig`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/SAT/ClauseConfig.lean by skeleton subtraction
import Mathlib

/-!
# Literals, clauses, CNF formulas and clause configurations

This module supplies the propositional syntax used by
`Bridges/PosetTheory/TropicalClauseSpace.lean`, which had no module providing it.

* `Literal n` — a positive or negative literal on `n` variables;
* `Clause n` — a finite set of literals, `CNFFormula n` — a finite set of clauses;
* `Assignment n`, `Literal.satisfiedBy`, `CNFFormula.satisfiedBy`, `CNFFormula.IsUnsat`;
* `Config n s` — a *clause configuration*: a set of at most `s` simultaneously active
  clauses, the proof-state model whose tropical geometry is studied downstream.
-/

/-- A literal on `n` propositional variables. -/
inductive Literal (n : ℕ) where
  | pos : Fin n → Literal n
  | neg : Fin n → Literal n
deriving DecidableEq, Repr

instance (n : ℕ) : Fintype (Literal n) :=
  Fintype.ofEquiv (Fin n ⊕ Fin n)
    { toFun := fun x => match x with
        | Sum.inl i => Literal.pos i
        | Sum.inr i => Literal.neg i
      invFun := fun l => match l with
        | Literal.pos i => Sum.inl i
        | Literal.neg i => Sum.inr i
      left_inv := by rintro (i | i) <;> rfl
      right_inv := by rintro (l | l) <;> rfl }

/-- A clause: a finite set of literals, read disjunctively. -/
abbrev Clause (n : ℕ) := Finset (Literal n)

/-- A CNF formula: a finite set of clauses, read conjunctively. -/
abbrev CNFFormula (n : ℕ) := Finset (Clause n)

/-- A Boolean assignment of the `n` variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- The empty clause, the unsatisfiable one. -/
def emptyClause (n : ℕ) : Clause n := (∅ : Finset (Literal n))

namespace Literal

/-- When a literal is satisfied by an assignment. -/
def satisfiedBy {n : ℕ} : Literal n → Assignment n → Prop
  | Literal.pos i, σ => σ i = true
  | Literal.neg i, σ => σ i = false

instance {n : ℕ} (l : Literal n) (σ : Assignment n) : Decidable (l.satisfiedBy σ) := by
  cases l <;> unfold satisfiedBy <;> infer_instance

end Literal

namespace CNFFormula

/-- A CNF formula is satisfied when every clause has a satisfied literal. -/
def satisfiedBy {n : ℕ} (F : CNFFormula n) (σ : Assignment n) : Prop :=
  ∀ C ∈ F, ∃ l ∈ C, Literal.satisfiedBy l σ

/-- A CNF formula is unsatisfiable when no assignment satisfies it. -/
def IsUnsat {n : ℕ} (F : CNFFormula n) : Prop :=
  ∀ σ : Assignment n, ¬ F.satisfiedBy σ


end CNFFormula

/-- A **clause configuration**: the set of clauses simultaneously active in a proof
state, of size at most `s`. -/
structure Config (n s : ℕ) where
  /-- The active clauses. -/
  clauses : Finset (Clause n)
  /-- The configuration respects the space bound. -/
  hsize : clauses.card ≤ s
deriving DecidableEq

/-- The empty configuration. -/
def emptyConfig (n s : ℕ) : Config n s :=
  ⟨(∅ : Finset (Clause n)), by simp⟩


