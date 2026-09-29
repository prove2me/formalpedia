-- Prove2me | solution 1 for MindTools.Bounded.wellFounded_not_total
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:23:17.512681+00:00
-- url     : https://prove2.me/submissions/8e96445b-5964-4cf0-8468-56e47a36d16e

-- Sol generated from Logic/MindToolsBoundedApprehension.lean
import Mathlib
import Definitions.Def_Logic_MindTools
import Definitions.Def_Logic_MindToolsBoundedApprehension
import Theorems.Thm_MindTools_hierarchy_wellFounded_of_ordinalRanks

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



/-- The two sample theories are incomparable and distinct. -/
theorem toolZero_toolOne_incomparable :
    ¬ Stronger toolZero toolOne ∧ ¬ Stronger toolOne toolZero ∧ toolZero ≠ toolOne := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : (1 : ℕ) ∈ ({0} : Set ℕ) := h.1 rfl
    simp at this
  · have : (0 : ℕ) ∈ ({1} : Set ℕ) := h.1 rfl
    simp at this
  · have : (0 : ℕ) ∈ ({1} : Set ℕ) := by
      rw [show ({1} : Set ℕ) = toolOne.provable from rfl, ← h]; rfl
    simp at this




open MindTools.Bounded in
theorem solution:
    ∃ (tools : Bool → FormalSystem ℕ) (rank : Bool → Ordinal),
      OrdinalRanks tools rank ∧
      WellFounded (fun i j : Bool => Stronger (tools j) (tools i)) ∧
      ¬ (∀ i j, Stronger (tools i) (tools j) ∨ Stronger (tools j) (tools i) ∨
          tools i = tools j) := by
  obtain ⟨h01, h10, hne⟩ := toolZero_toolOne_incomparable
  have hrank : OrdinalRanks sampleTools (fun _ => 0) := by
    intro i j hij
    rcases i <;> rcases j <;> simp only [sampleTools, if_true] at hij
    · exact absurd hij (ssubset_irrefl _)
    · exact absurd hij h01
    · exact absurd hij h10
    · exact absurd hij (ssubset_irrefl _)
  refine ⟨sampleTools, fun _ => 0, hrank,
    hierarchy_wellFounded_of_ordinalRanks _ _ hrank, fun htot => ?_⟩
  rcases htot true false with h | h | h
  · exact h01 (by simpa [sampleTools] using h)
  · exact h10 (by simpa [sampleTools] using h)
  · exact hne (by simpa [sampleTools] using h)
