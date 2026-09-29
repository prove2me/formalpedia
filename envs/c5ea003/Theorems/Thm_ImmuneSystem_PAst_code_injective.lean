-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_code_injective
-- name    : ImmuneSystem.PAst.code_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:44:00.04897+00:00
-- url     : https://prove2.me/theorems/5a1d7193-6d35-4bde-a724-65ebb856ab47
-- title:
--   Attestation is faithful.
-- statement:
--   **Attestation is faithful.**  Distinct ASTs get distinct attestation tags.
--
--   ```lean
--   theorem ImmuneSystem.PAst.code_injective: Function.Injective code := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneAstCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneAstCore.lean#L80

-- Thm stub generated from Shared/ImmuneAstCore.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore

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

open ImmuneSystem


open PAst

theorem ImmuneSystem.PAst.code_injective: Function.Injective code := by sorry
