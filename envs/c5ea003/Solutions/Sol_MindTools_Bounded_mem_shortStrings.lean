-- Prove2me | solution 1 for MindTools.Bounded.mem_shortStrings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:09:33.184983+00:00
-- url     : https://prove2.me/submissions/f676af7c-8657-4fbc-b609-30ed5809dfc1

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
theorem solution{n : ℕ} {l : List Bool} :
    l ∈ shortStrings n ↔ l.length ≤ n := by
  induction n generalizing l with
  | zero =>
      simp [shortStrings, List.length_eq_zero_iff]
  | succ n ih =>
      constructor
      · intro hl
        simp only [shortStrings, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hl
        rcases hl with rfl | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) <;> simp
        · exact ih.1 ht
        · exact ih.1 ht
      · intro hl
        match l with
        | [] => simp [shortStrings]
        | (true :: t) =>
            have : t.length ≤ n := by simpa using hl
            simp only [shortStrings, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨t, ih.2 this, rfl⟩)
        | (false :: t) =>
            have : t.length ≤ n := by simpa using hl
            simp only [shortStrings, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨t, ih.2 this, rfl⟩)
