-- Prove2me | solution 1 for MindTools.Bounded.card_shortStrings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:09:32.627738+00:00
-- url     : https://prove2.me/submissions/3b17e391-fb00-4a02-8235-4e11c7964613

-- Sol generated from Logic/MindToolsBoundedApprehension.lean
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







open MindTools.Bounded in
theorem solution(n : ℕ) : (shortStrings n).card = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [shortStrings]
  | succ n ih =>
      have hdisj : Disjoint ((shortStrings n).image (List.cons true))
          ((shortStrings n).image (List.cons false)) := by
        simp [Finset.disjoint_left]
      have hnot : ([] : List Bool) ∉ ((shortStrings n).image (List.cons true)) ∪
          ((shortStrings n).image (List.cons false)) := by simp
      have hA : ((shortStrings n).image (List.cons true)).card = (shortStrings n).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have hB : ((shortStrings n).image (List.cons false)).card = (shortStrings n).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      rw [shortStrings, Finset.card_insert_of_notMem hnot,
        Finset.card_union_of_disjoint hdisj, hA, hB, ih]
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega
