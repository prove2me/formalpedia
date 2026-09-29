-- Prove2me | Theorems.Thm_MindTools_Bounded_wellFounded_not_total
-- name    : MindTools.Bounded.wellFounded_not_total
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:35:30.36528+00:00
-- url     : https://prove2.me/theorems/ab6cb1f1-5b84-44f7-a012-ba65430ccff9
-- title:
--   The sample family is ordinal-ranked (vacuously: no strict comparison holds),
-- statement:
--   The sample family is ordinal-ranked (vacuously: no strict comparison holds),
--   so by `hierarchy_wellFounded_of_ordinalRanks` its strength order is
--   well-founded — yet the two tools are incomparable.  Well-foundedness of a
--   hierarchy of mind tools therefore does *not* imply that all tools are
--   comparable.
--
--   ```lean
--   theorem MindTools.Bounded.wellFounded_not_total:
--       ∃ (tools : Bool → FormalSystem ℕ) (rank : Bool → Ordinal),
--         OrdinalRanks tools rank ∧
--         WellFounded (fun i j : Bool => Stronger (tools j) (tools i)) ∧
--         ¬ (∀ i j, Stronger (tools i) (tools j) ∨ Stronger (tools j) (tools i) ∨
--             tools i = tools j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MindToolsBoundedApprehension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MindToolsBoundedApprehension.lean#L311

-- Thm stub generated from Logic/MindToolsBoundedApprehension.lean
import Mathlib
import Definitions.Def_Logic_MindTools
import Definitions.Def_Logic_MindToolsBoundedApprehension

/-!
# Resource-bounded apprehension: unconditional mind tools

The previous development (`Catalog/Logic/MindTools.lean`) treats "directly
apprehended by a human brain" as an undefined set-valued parameter, so every
mind-tool statement there is *conditional*: it needs a certificate consisting of
a containment and a theorem certified not to be apprehended.

This file carries out natural extensions 2, 3, 6 and 7 of the programme:

* **Bounded apprehension (2).**  We replace the psychological predicate by a
  *resource bound*: a sentence is apprehended at level `b` when it has a proof
  of size at most `b` in a fixed proof system.  This is a mathematically
  testable notion.
* **Unconditional certificates (3).**  For proof systems with finitely many
  proofs of each size and infinitely many theorems, both premises of the
  conditional theorem are *discharged*: the containment holds by definition and
  the inaccessible witness exists by counting (`isMindTool_of_infinite`).  For
  proof systems whose proofs are binary strings we get an explicit numerical
  witness: some sentence below `2 ^ (b + 1)` has no proof of size `≤ b`
  (`exists_lt_two_pow_not_apprehended`), by a pigeonhole count of the
  `2 ^ (b + 1) - 1` binary strings of length at most `b`.
* **Concrete ranks (6).**  The bounded-apprehension family is ranked by its own
  resource bound, and this ranking satisfies `MindTools.OrdinalRanks`, hence the
  hierarchy is well-founded.
* **Well-founded but not linear (7).**  A two-element family of theories is
  exhibited which is ordinal-ranked (hence well-founded) yet contains
  incomparable tools, so well-foundedness of the hierarchy does not upgrade to
  comparability.
-/

open MindTools
open Bounded

universe u


variable {Sentence : Type u}





/-! ### Premise (1) is automatic for bounded apprehension -/




/-! ### Premise (2) by counting -/




/-! ### Concrete ranks for the bounded hierarchy (extension 6) -/





/-! ### Binary proof systems and an explicit pigeonhole witness -/








/-! ### A fully concrete instance: the length code -/






/-! ### Well-founded does not mean linearly ordered (extension 7) -/

theorem MindTools.Bounded.wellFounded_not_total:
    ∃ (tools : Bool → FormalSystem ℕ) (rank : Bool → Ordinal),
      OrdinalRanks tools rank ∧
      WellFounded (fun i j : Bool => Stronger (tools j) (tools i)) ∧
      ¬ (∀ i j, Stronger (tools i) (tools j) ∨ Stronger (tools j) (tools i) ∨
          tools i = tools j) := by sorry
