-- Prove2me | solution 1 for MindTools.hierarchy_wellFounded_of_ordinalRanks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:19:46.194586+00:00
-- url     : https://prove2.me/submissions/d2a59518-8e8c-437c-bc97-9f00e65fc670

-- Sol generated from Logic/MindTools.lean
import Mathlib
import Definitions.Def_Logic_MindTools
import Mathlib.Data.Set.Lattice
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Mind tools as strict extensions of direct apprehension

The informal phrase “the human brain can directly apprehend” has no canonical
mathematical definition.  This file therefore isolates it as a set-valued
parameter.  The resulting theorems state exactly which certificates are needed
for claims about a named formal system; in particular, no claim about ZFC is
smuggled in as an axiom.
-/

open MindTools





/-
The simplest usable certificate for a mind tool consists of containment and
one theorem outside direct apprehension.
-/

/-
A concrete inaccessible theorem and closure of direct reasoning certify a
mind tool.
-/

/-
Strictly increasing proof strength preserves the mind-tool property.
-/

/-
Proof-theoretic strength is transitive.
-/

/-
Consequently an entire two-step hierarchy above a mind tool still extends
cognition.
-/

/-
A faithful formal version of the proposed ZFC claim: a formalized ZFC is a
mind tool once supplied with closure and a specific ZFC theorem not directly
apprehended.  Gödel incompleteness alone does not manufacture the final premise.
-/


/-
A stronger tool inherits every uniformly solved class.
-/

/-
A uniform family plus one genuinely new theorem yields strict superiority.
This captures the precise content available from “all categories at once”:
uniformity is useful only when accompanied by a theorem unavailable below.
-/

/-
The uniform categorical certificate also transports the mind-tool property
from the weaker set-theoretic tool.
-/


/-
The proposed ordinal ranking has a rigorous consequence: there is no
infinite descending chain of tools whose direction is strict increase in
proof-theoretic strength.
-/


open MindTools in
theorem solution{ι Sentence : Type*}
    (tools : ι → FormalSystem Sentence) (rank : ι → Ordinal)
    (hrank : OrdinalRanks tools rank) :
    WellFounded (fun i j => Stronger (tools j) (tools i)) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s hs
  obtain ⟨m, hm⟩ : ∃ m ∈ Set.image rank s,
      ∀ n ∈ Set.image rank s, m ≤ n := by
    exact ⟨InfSet.sInf (rank '' s), csInf_mem (Set.Nonempty.image _ hs),
      fun n hn => csInf_le' hn⟩
  rcases hm with ⟨⟨x, hx, rfl⟩, hm⟩
  exact ⟨x, hx, fun y hy hxy =>
    not_lt_of_ge (hm _ (Set.mem_image_of_mem _ hy)) (hrank _ _ hxy)⟩
