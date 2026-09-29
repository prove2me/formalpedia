-- Prove2me | Theorems.Thm_MachineLearning_CommittedPCPThreeColoringZK_perm3_exists
-- name    : MachineLearning.CommittedPCPThreeColoringZK.perm3_exists
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:42:56.613485+00:00
-- url     : https://prove2.me/theorems/e1d1952a-5274-4ddd-8216-13a6a314d787
-- title:
--   Existence half of sharp 2-transitivity: some colour permutation maps a
-- statement:
--   **Existence half of sharp 2-transitivity**: some colour permutation maps a
--   given pair of distinct colours to any other pair of distinct colours.
--
--   ```lean
--   theorem MachineLearning.CommittedPCPThreeColoringZK.perm3_exists(x y a b : ZMod 3) (hxy : x ≠ y) (hab : a ≠ b) :
--       ∃ π : Equiv.Perm (ZMod 3), π x = a ∧ π y = b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CommittedPCPThreeColoringZK.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CommittedPCPThreeColoringZK.lean#L82

-- Thm stub generated from MachineLearning/CommittedPCPThreeColoringZK.lean
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK
import Definitions.Def_MachineLearning_CommittedPCPThreeColoringZK

/-!
# An end-to-end instance: the committed 2-query PCP for graph 3-colouring is perfect HVZK

This file instantiates the general composition theorem of
`MachineLearning/CommittedLocalOracleZK.lean` on the canonical constant-query
local verifier: the 2-query PCP for graph 3-colourability (the verifier of
`Bridges/PCPLocalVerifier.lean` and `Shared/ZeroKnowledge/PCPBridge.lean`),
compiled with the coordinate-wise one-time-pad commitment.

* proof string: a proper 3-colouring `c : V → ZMod 3`, randomized by a uniform
  colour permutation `π` (the prover's randomness);
* verifier randomness: a uniformly chosen edge `r ∈ E`, whose two endpoints are
  the **two** queried coordinates;
* commitment: the one-time pad `v ↦ π (c v) + ρ v`, opened at the queried
  coordinates by revealing the pad there.

The simulator `zkSim` never looks at `c`: on the challenged edge it simply picks a
uniformly random *ordered pair of distinct colours*.

## Main results

* `perm3_card_eq_one` — for distinct `x ≠ y` and distinct targets `a ≠ b`, exactly
  one permutation of `ZMod 3` sends `x ↦ a, y ↦ b`. (Sharp 2-transitivity of `S₃`.)
* `zkSim_perfectly_simulates` — the local view of the two opened colours is
  *exactly* the uniform distribution on ordered distinct pairs, hence perfectly
  simulatable without the colouring.
* `threeColoring_perfect_hvzk` — **the compiled protocol is perfect
  honest-verifier zero knowledge**: the real transcript distribution equals the
  simulated one on the nose.
* `threeColoring_query_le_two` — the transcript reveals at most two proof symbols.
* `threeColoring_completeness` — the two opened symbols always differ, so the
  honest verifier always accepts.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the whole zero-knowledge content of the GMW-style
committed PCP for 3-colouring is the *sharp 2-transitivity of `S₃`* on colours:
the permutation randomness turns the two opened colours into a uniformly random
ordered distinct pair, independent of the witness.

Experiment (Experimenter): built the explicit bijection
`Φ π = (π (c x), π (c y))` from `Equiv.Perm (ZMod 3)` to ordered distinct pairs.
Surjectivity is an explicit two-swap construction (`perm3_exists`); injectivity
is the statement that a permutation of a 3-element set is determined by its
values at two points (`perm3_unique`), which needs the finite fact
`zmod3_third_unique`, proved by `decide` on 81 cases.

Analysis (Analyst): the bijection does *two* jobs at once — it equates the
cardinalities of the prover's and the simulator's randomness spaces, and it
matches the fibres of the "opened view" map. That is exactly the data the general
theorem `perfect_hvzk` consumes, so no case analysis on transcripts is needed
here. Attempting the fibre-matching by brute-force `decide` over
`Equiv.Perm (ZMod 3)` did not terminate: structural bijections beat enumeration.

Critique (Critic): the result is stated for a *proper* colouring, which is
exactly the honest-prover case; without properness the two opened symbols could
coincide and the simulated distribution (which never outputs equal colours) would
differ — so the hypothesis is load-bearing, not decoration. Self-loops in `E` are
automatically excluded by properness.

Synthesis (PI): locality (2 queries) + hiding (one-time pad) + a sharply
2-transitive symmetry of the alphabet = perfect zero knowledge, with no
statistical slack.
-- !-- Lab Notes -- !--
-/

open MachineLearning.CommittedPCPThreeColoringZK

open Finset MachineLearning.CommittedLocalOracleZK

/-! ## Sharp 2-transitivity of the colour symmetry group -/

theorem MachineLearning.CommittedPCPThreeColoringZK.perm3_exists(x y a b : ZMod 3) (hxy : x ≠ y) (hab : a ≠ b) :
    ∃ π : Equiv.Perm (ZMod 3), π x = a ∧ π y = b := by sorry
