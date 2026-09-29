-- Prove2me | solution 1 for MindTools.Bounded.exists_lt_two_pow_not_apprehended
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:19:45.668977+00:00
-- url     : https://prove2.me/submissions/3187f397-126b-41a3-9f19-6f7c6ab0c6f8

-- Sol generated from Logic/MindToolsBoundedApprehension.lean
import Mathlib
import Definitions.Def_Logic_MindTools
import Definitions.Def_Logic_MindToolsBoundedApprehension
import Theorems.Thm_MindTools_Bounded_card_shortStrings
import Theorems.Thm_MindTools_Bounded_mem_shortStrings

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





/-- Consequently fewer than `2 ^ (n + 1)` sentences can be reached by proofs of
size at most `n`. -/
theorem card_shortStrings_lt (n : ℕ) : (shortStrings n).card < 2 ^ (n + 1) := by
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have h2 := card_shortStrings n
  omega



/-! ### A fully concrete instance: the length code -/






/-! ### Well-founded does not mean linearly ordered (extension 7) -/







open MindTools.Bounded in
theorem solution(c : List Bool → ℕ) (b : ℕ) :
    ∃ n < 2 ^ (b + 1), n ∉ (apprehends (binary c) b).direct := by
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.range (2 ^ (b + 1)) ⊆ (shortStrings b).image c := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := hcon n (Finset.mem_range.1 hn)
    exact Finset.mem_image.2 ⟨p, mem_shortStrings.2 hp, rfl⟩
  have h1 : 2 ^ (b + 1) ≤ ((shortStrings b).image c).card := by
    simpa using Finset.card_le_card hsub
  have h2 : ((shortStrings b).image c).card ≤ (shortStrings b).card := Finset.card_image_le
  have h3 := card_shortStrings_lt b
  omega
