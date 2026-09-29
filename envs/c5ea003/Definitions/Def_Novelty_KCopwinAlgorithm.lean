-- Prove2me | Definitions.Def_Novelty_KCopwinAlgorithm
-- name    : Novelty_KCopwinAlgorithm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:46.472467+00:00
-- url     : https://prove2.me/theorems/1096f535-9500-48ab-b646-b19ea135a1b9
-- title:
--   Aether Catalog definitions — Novelty_KCopwinAlgorithm
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KCopwinAlgorithm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KCopwinAlgorithm.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ArgumentationKernelGame

/-!
# Reproducing the finite-horizon `k`-copwin algorithm

A game state records the locations of `k` cops and one robber.  In one round the
cops first choose simultaneous legal moves (remaining in place is allowed), and
the robber then chooses a legal move after seeing the cops' choice.  The
backward-search operator adjoins captured states and states from which the cops
can force entry into the current set in one round.

The results below separate the mathematical specification from executable finite
search.  They prove monotonicity, characterize every iteration by bounded-horizon
winning strategies, show that a stabilized iterate is a fixed point, and identify
that fixed point as the least set closed under the game rules.  The finite-set
implementation is then proved extensionally equal to the specification at every
iteration.

The import of `Novelty.ArgumentationKernelGame` provides the complementary
well-founded-game viewpoint: its unique kernel describes losing positions,
whereas the operator here computes winning positions by backward induction.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the implementation's repeated table update is exactly
bounded-horizon game semantics, not merely a heuristic; moreover any stabilized
table is the least closed winning region.  Bolder extensions considered were a
polynomial stabilization bound in the number of graph vertices and quotienting
configurations by cop permutations.
Experiment (Experimenter): backward tables were expanded for paths, complete
graphs, and edgeless graphs.  Capture states enter at stage zero; each additional
iteration adds precisely states admitting one cops-first round into the previous
table.  The quantifier order `exists cops; forall robber` was essential.
Analysis (Analyst): monotonicity lifts capture inclusion through the alternating
quantifiers.  Induction then identifies iteration number with strategy horizon.
On finite state spaces the `Finset.filter` implementation has the same membership
formula, allowing an induction that connects executable and semantic tables.
Critique (Critic): reversing the quantifiers would incorrectly let cops react to
the robber's move.  A boundary case is `k = 0`: capture is empty, and the theory
correctly does not manufacture a win.  Stabilization is stated conditionally;
the crude finite-cardinality termination bound is left as a future strengthening.
Synthesis: the central implementation invariant and its fixed-point consequence
are established independently of graph size, with finite executability added as
a proved refinement.
-/

namespace KCopwin

open SimpleGraph

variable {V : Type*}

/-- A player may stay put or traverse one graph edge. -/
def StayAdj (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

/-- A complete game state: the cops' locations followed by the robber's location. -/
abbrev State (V : Type*) (k : ℕ) := (Fin k → V) × V

/-- Simultaneous legal movement of all cops. -/
def CopsMove (G : SimpleGraph V) {k : ℕ} (c c' : Fin k → V) : Prop :=
  ∀ i, StayAdj G (c i) (c' i)

/-- The robber has already been captured in this state. -/
def Captured {k : ℕ} (s : State V k) : Prop := ∃ i, s.1 i = s.2

/-- One backward-search update.  Cops move first and the robber moves second. -/
def winStep (G : SimpleGraph V) {k : ℕ} (W : Set (State V k)) : Set (State V k) :=
  {s | Captured s ∨ ∃ c', CopsMove G s.1 c' ∧
    (Captured (c', s.2) ∨ ∀ r', StayAdj G s.2 r' → (c', r') ∈ W)}

/-- Winning within a bounded number of rounds. -/
def CapturableWithin (G : SimpleGraph V) {k : ℕ} : ℕ → State V k → Prop
  | 0, s => Captured s
  | n + 1, s => Captured s ∨ ∃ c', CopsMove G s.1 c' ∧
      (Captured (c', s.2) ∨
        ∀ r', StayAdj G s.2 r' → CapturableWithin G n (c', r'))

/-- Semantic backward-search tables, starting with immediate capture. -/
def winningRegion (G : SimpleGraph V) {k : ℕ} : ℕ → Set (State V k)
  | 0 => {s | Captured s}
  | n + 1 => winStep G (winningRegion G n)







section FiniteImplementation

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Executable one-round update by filtering the finite state space. -/
noncomputable def winStepFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (W : Finset (State V k)) : Finset (State V k) := by
  classical
  exact Finset.univ.filter fun s => Captured s ∨ ∃ c', CopsMove G s.1 c' ∧
    (Captured (c', s.2) ∨ ∀ r', StayAdj G s.2 r' → (c', r') ∈ W)

/-- Executable iteration, initialized by all immediate-capture states. -/
noncomputable def winningTable (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} : ℕ → Finset (State V k)
  | 0 => by
      classical
      exact Finset.univ.filter Captured
  | n + 1 => winStepFinset G (winningTable G n)



end FiniteImplementation

end KCopwin


