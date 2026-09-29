-- Prove2me | Definitions.Def_Novelty_DreamLogic
-- name    : Novelty_DreamLogic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:16:39.180924+00:00
-- url     : https://prove2.me/theorems/e3703d06-09b7-4120-af72-923b94fdc848
-- title:
--   Aether Catalog definitions — Novelty_DreamLogic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.DreamLogic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/DreamLogic.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ArgumentationCore

/-!
# Dream logic: contradictory evidence, revision, and finitary openness

This study separates three ideas often compressed into the phrase “dream logic.”
A signed information state can support both an assertion and its denial without
supporting every assertion. A revision operation may retract the opposite sign,
so accepted information is non-monotone in time. Finally, finite information
states form a finitary topology: they are stable under finite unions and finite
intersections, but an infinite union can escape the class.

The last structure is deliberately called a *finitary topology*, rather than a
topology. Ordinary topologies are closed under arbitrary unions by definition;
the failure of arbitrary-union closure is therefore a boundary theorem, not an
example of an exotic topology.
-/

namespace DreamLogic

/-- A literal is an atom equipped with a sign: `true` is positive evidence and
`false` is negative evidence. -/
abbrev Literal (Atom : Type*) := Atom × Bool

/-- Flip the sign of a literal. -/
def opposite {Atom : Type*} (l : Literal Atom) : Literal Atom := (l.1, !l.2)




/-- A belief state accepts exactly the literals it contains. -/
def Entails {Atom : Type*} (B : Set (Literal Atom)) (l : Literal Atom) : Prop := l ∈ B

/-- An atom is contradictory in `B` when both signs are accepted. -/
def Contradictory {Atom : Type*} (B : Set (Literal Atom)) (a : Atom) : Prop :=
  (a, true) ∈ B ∧ (a, false) ∈ B

/-- Revision accepts `l` and retracts its opposite. -/
def revise {Atom : Type*} (B : Set (Literal Atom)) (l : Literal Atom) :
    Set (Literal Atom) := insert l (B \ {opposite l})

/-
Revision accepts its new literal while rejecting the contrary literal.
-/

/-
A direct contradiction is not explosive: with at least two atoms, the state
containing both signs of `a` need not entail a positive assertion about `b`.
-/

/-
Retraction makes revision genuinely non-monotone: revising a contradictory
state by either of its literals loses information from the old state.
-/

/-
Successive contrary revisions are order-sensitive. The latest sign wins.
-/

/-- Complementary literals attack one another. This imports the argumentation
viewpoint into signed evidence. -/
def contraryAttack {Atom : Type*} (l k : Literal Atom) : Prop := k = opposite l

/-- Semantic consistency means that no atom carries both signs. -/
def Consistent {Atom : Type*} (B : Set (Literal Atom)) : Prop :=
  ∀ a, ¬ Contradictory B a

/-
Consistency is exactly conflict-freedom for the complementary attack graph.
-/

/-
Revision preserves global consistency: it removes the unique sign that could
conflict with the newly accepted literal.
-/

/-! ## Finitary openness -/


namespace FinitaryOpen

variable {X : Type*}




/-
Any finite union of finitary opens remains finitarily open.
-/


/-
The union of all singleton states on `ℕ` is the whole space.
-/

/-
**Arbitrary-union obstruction.** Although every singleton of `ℕ` is
finitarily open, their countable union is not. Thus these opens satisfy the
finite lattice laws but cannot be the opens of a topology containing the whole
space.
-/

end FinitaryOpen


/-
Revision is an internal dynamic on finite opens.
-/

/-
**Logic–argumentation–topology bridge.** A finite consistent dream state is
simultaneously a finitary open and a conflict-free set in the complementary
attack graph; revision remains inside both classes.
-/

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer), ranked by expected impact:
-- (1) signed paraconsistent states admit a common representation as
--     conflict-free argument sets and finitary opens after revision;
-- (2) every finite sequence of revisions has a canonical normal form determined
--     by the last occurrence of each atom;
-- (3) revision trajectories form directed paths in the face graph of the
--     complementary-attack complex;
-- (4) compactness of an ambient information topology characterizes when local
--     finite dream fragments assemble into a global state;
-- (5) arbitrary-union failure is exactly the obstruction to treating finite
--     epistemic states as an ordinary topology;
-- (6) contradiction without explosion persists under every irrelevant revision.
-- The first four are cross-domain conjectures joining dynamics, argumentation,
-- combinatorial topology, and compactness.
-- Experiment (Experimenter): the four states over one atom were enumerated.
-- Revision by the positive sign sends the empty, positive-only, negative-only,
-- and contradictory states respectively to positive-only in every case; negative
-- revision behaves symmetrically. On two atoms, the contradictory state at the
-- first atom omits both signs of the second, directly falsifying explosion.
-- Analysis (Analyst): two independent boundaries emerged. Complementary attack
-- converts consistency into conflict-freedom, while revision removes exactly one
-- attacker before inserting its target. Separately, finite subsets have all
-- finite lattice operations but the union of the natural-number singletons is
-- infinite. These combine in `revision_bridge` but should not be conflated:
-- paraconsistency is semantic, arbitrary-union failure is a size restriction.
-- Critique (Critic): ordinary topological spaces cannot have opens that fail
-- arbitrary-union closure. The correct object is therefore explicitly named a
-- finitary topology. Non-explosion requires distinct atoms; without that guard,
-- the alleged unrelated conclusion could be one side of the contradiction.
-- None of the bridge results identifies consistency with absence of all attacks;
-- it uses the specific complementary attack relation.
-- Synthesis (Principal Investigator): signed sets provide the smallest model
-- supporting coexistence and retraction. The imported conflict-free semantics
-- supplies the argumentation bridge, and finite support supplies a precise
-- pretopological boundary. The resulting revision dynamic preserves both the
-- semantic and finitary invariants.
-- !-- End Lab Notes -- !--

end DreamLogic


