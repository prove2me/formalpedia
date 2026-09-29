-- Prove2me | Definitions.Def_Shared_ImmuneAstCore
-- name    : Shared_ImmuneAstCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:56:05.817031+00:00
-- url     : https://prove2.me/theorems/c8123b88-8ae9-4efd-856b-96f3a5ed8fa7
-- title:
--   Aether Catalog definitions — Shared_ImmuneAstCore
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneAstCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneAstCore.lean by skeleton subtraction
import Mathlib

/-!
# Algorithmic Immune System, Part I: the parasite calculus and structural attestation

This file sets up the syntactic layer of an *algorithmic immune system*: a runtime
that guards a program against arbitrary, unknown, self-modifying mutations of its
own abstract syntax tree.

The object language `PAst` (*parasite calculus*) is deliberately minimal but has
exactly the three ingredients that make self-modifying malware possible:

* `PAst.inp` — the *self register*.  At top level the runtime feeds a program its
  own source code (Section II), so `inp` is a genuine quine primitive: a program
  can read (and reason about) its own AST.
* `PAst.call f a` — invocation of a *fixed subprogram* `f` on a computed argument.
  This lets a parasite invoke a detector on itself.
* `PAst.attack` — the single observable, forbidden side effect.

`PAst.ite` gives branching and `PAst.lit` constants.

The main results here are purely structural and are the foundation of the
attestation mechanism used in Part III:

* `PAst.code_injective` : the Gödel numbering `PAst.code` is injective, so a
  structural attestation tag identifies an AST uniquely;
* `PAst.code_eq_iff`   : attestation equality is exactly AST equality;
* `PAst.size_pos`, `PAst.size_lt_of_mem_children` : the well-founded size measure
  used for the counting arguments in Part III.
-/

namespace ImmuneSystem

/-- The *parasite calculus*: a minimal AST with a self register, first-class
subprogram invocation and one observable forbidden effect. -/
inductive PAst : Type
  | inp : PAst
  | attack : PAst
  | lit : ℕ → PAst
  | ite : PAst → PAst → PAst → PAst
  | call : PAst → PAst → PAst
  deriving DecidableEq, Repr

namespace PAst

/-- Number of nodes of an AST. -/
def size : PAst → ℕ
  | inp => 1
  | attack => 1
  | lit _ => 1
  | ite c a b => 1 + size c + size a + size b
  | call f a => 1 + size f + size a



/-- Structural attestation tag (a Gödel numbering of ASTs).  The residue mod `5`
records the head constructor; the payload is packed with Cantor pairing. -/
def code : PAst → ℕ
  | inp => 0
  | attack => 1
  | lit n => 5 * n + 2
  | ite c a b => 5 * (Nat.pair (Nat.pair (code c) (code a)) (code b)) + 3
  | call f a => 5 * (Nat.pair (code f) (code a)) + 4




end PAst

end ImmuneSystem


