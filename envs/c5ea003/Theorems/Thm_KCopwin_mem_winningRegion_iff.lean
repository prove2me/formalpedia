-- Prove2me | Theorems.Thm_KCopwin_mem_winningRegion_iff
-- name    : KCopwin.mem_winningRegion_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:03:42.146395+00:00
-- url     : https://prove2.me/theorems/726ea10e-04f4-49fc-bce5-dfe0acf38509
-- title:
--   Iteration invariant.
-- statement:
--   **Iteration invariant.** Membership in table `n` is equivalent to a cops
--   strategy forcing capture in at most `n` rounds.
--
--   ```lean
--   theorem KCopwin.mem_winningRegion_iff(G : SimpleGraph V) {k : ℕ} (n : ℕ) (s : State V k) :
--       s ∈ winningRegion G n ↔ CapturableWithin G n s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KCopwinAlgorithm.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KCopwinAlgorithm.lean#L106

-- Thm stub generated from Novelty/KCopwinAlgorithm.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationKernelGame
import Definitions.Def_Novelty_KCopwinAlgorithm

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

open KCopwin

open SimpleGraph

variable {V : Type*}

theorem KCopwin.mem_winningRegion_iff(G : SimpleGraph V) {k : ℕ} (n : ℕ) (s : State V k) :
    s ∈ winningRegion G n ↔ CapturableWithin G n s := by sorry
