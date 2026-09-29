-- Prove2me | Definitions.Def_Evergreen_Bootstrapping_SelfReference
-- name    : Evergreen_Bootstrapping_SelfReference
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:36:30.73852+00:00
-- url     : https://prove2.me/theorems/3670d398-b2c7-4f33-a836-22544be0c121
-- title:
--   Aether Catalog definitions — Evergreen_Bootstrapping_SelfReference
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Bootstrapping.SelfReference`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Bootstrapping/SelfReference.lean by skeleton subtraction
import Mathlib
/-
  # Self-Reference and Diagonal Bootstrapping
  ==============================================

  The diagonal argument is the engine of self-reference: a structure examines
  itself and, through that examination, creates something new. We formalize
  Lawvere's categorical fixed-point theorem, which unifies Cantor's theorem,
  Gödel's incompleteness, the halting problem, and Tarski's undefinability
  into a single bootstrap.

  Key insight: If a structure can "talk about itself" (via a surjection A → (A → B)),
  then every endomorphism on B has a fixed point. This is the universal bootstrap.
-/


/-! ## Lawvere's Fixed Point Theorem

Given a surjection φ : A → (A → B), every function g : B → B has a fixed point.
This is the most general bootstrap theorem in mathematics.

Proof: Define h(a) = g(φ(a)(a)) — the diagonal. Since φ is surjective,
∃ a₀ with φ(a₀) = h. Then:
  h(a₀) = g(φ(a₀)(a₀)) = g(h(a₀))
So h(a₀) is a fixed point of g. The diagonal creates the self-reference. -/



/-! ## The Diagonal Lemma (Gödel's Self-Reference)

In any sufficiently powerful formal system, for any formula φ(x), there exists
a sentence σ such that the system proves σ ↔ φ(⌜σ⌝). The sentence "talks about
itself" through Gödel numbering.

We formalize this abstractly: given a way to represent and substitute, diagonal
sentences exist.
-/

/-- Abstract representation of a formal system with self-reference capability -/
structure FormalSystem where
  Sentence : Type
  Provable : Sentence → Prop
  code : Sentence → ℕ
  code_injective : Function.Injective code
  numeral : ℕ → Sentence
  subst : Sentence → ℕ → Sentence

/-- A diagonalizable system: one where the diagonal lemma holds -/
class Diagonalizable (S : FormalSystem) where
  diagonal : (ℕ → Prop) → S.Sentence
  diagonal_spec : ∀ P : ℕ → Prop, S.Provable (diagonal P) ↔ P (S.code (diagonal P))


/-! ## Russell's Bootstrap Paradox

The set of all sets that don't contain themselves: R = {x | x ∉ x}.
Does R ∈ R? This self-referential question bootstraps a contradiction.
We show this forces any "set of all sets" construction to be inconsistent. -/


/-! ## Quine: The Self-Reproducing Bootstrap

A Quine is a program that outputs its own source code — pure bootstrapping.
We model this abstractly: in a computation model with a self-application
operator, Quines exist. -/

/-- Abstract model of computation with string output -/
structure ComputationModel where
  Program : Type
  run : Program → List Char
  expressive : ∀ s : List Char, ∃ p : Program, run p = s
  source : Program → List Char
  source_injective : Function.Injective source


