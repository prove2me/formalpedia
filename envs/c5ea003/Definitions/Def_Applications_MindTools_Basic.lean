-- Prove2me | Definitions.Def_Applications_MindTools_Basic
-- name    : Applications_MindTools_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:40.154192+00:00
-- url     : https://prove2.me/theorems/bb28e40e-e560-41f3-b3ce-7049f6112360
-- title:
--   Aether Catalog definitions — Applications_MindTools_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.MindTools.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/MindTools/Basic.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Common

/-!
# Mind Tools — Mathematics as Cognitive Extension (foundations)

This file gives a self-contained formal model of Rudy Rucker's notion of a
**mind tool**: a mathematical/formal structure that *extends* what a cognitive
agent can reach beyond what it can directly apprehend.

## The model

We work with an abstract space of `Statement`s.  We model a statement as a
*property of natural numbers* (`Set ℕ`); nothing below depends on this choice
except the incompleteness results, which use that the space of statements is
uncountable.  This is the "second-order arithmetic truth" reading: statements
are arbitrary predicates on the naturals.

A `FormalSystem` is identified with the set of statements it proves (its
theorems).  This is the extensional / Lindenbaum view of a theory.

* `LePow F G`  (`F ≼ G`) — *`G` is at least as powerful as `F`*: every theorem
  of `F` is a theorem of `G`.
* `LtPow F G`  (`F ≺ G`) — *`G` is strictly more powerful than `F`*.
* `Enumerable F` — the theorems of `F` can be listed by a function `ℕ → Statement`.
  This models "directly apprehensible / recursively enumerable" knowledge: a
  finite mind, or a finite axiomatization with a recursively enumerable proof
  system, only ever reaches countably many statements.
* `IsMindTool B F` — relative to a *brain* `B`, the system `F` is a mind tool
  iff it strictly extends `B` (`B ≺ F`): it proves things the brain does not.

The order-theoretic lemmas here (`≼` is a partial order, `≺` is a strict order,
incomparable systems exist) are used by the other files in this directory.
-/

namespace MindTools

/-- The space of statements.  A statement is modelled as a property of natural
numbers.  The only feature of this choice used below is that `Set ℕ` is
uncountable (Cantor), which drives the incompleteness phenomena. -/
abbrev Statement := Set ℕ

/-- A formal system, identified with the set of statements it proves. -/
@[ext]
structure FormalSystem where
  /-- The theorems of the system. -/
  Thm : Set Statement

/-- `F ≼ G`: `G` is at least as powerful as `F` — every theorem of `F` is a
theorem of `G`. -/
def LePow (F G : FormalSystem) : Prop := F.Thm ⊆ G.Thm

/-- `F ≺ G`: `G` is strictly more powerful than `F`. -/
def LtPow (F G : FormalSystem) : Prop := F.Thm ⊂ G.Thm

@[inherit_doc] scoped infix:50 " ≼ " => LePow
@[inherit_doc] scoped infix:50 " ≺ " => LtPow


/-- Relative to a brain `B`, a system `F` is a **mind tool** when it proves
strictly more than the brain can: `B ≺ F`. -/
def IsMindTool (B F : FormalSystem) : Prop := B ≺ F



/-! ### `≼` is a partial order -/




/-! ### `≺` is a strict order compatible with `≼` -/





theorem LtPow.lePow {F G : FormalSystem} (h : F ≺ G) : F ≼ G := h.subset



end MindTools


