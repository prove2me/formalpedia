-- Prove2me | Definitions.Def_MachineLearning_CommittedPCPThreeColoringZK
-- name    : MachineLearning_CommittedPCPThreeColoringZK
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:56.057867+00:00
-- url     : https://prove2.me/theorems/84d93212-439c-403e-b8d5-cc763c3cf0fb
-- title:
--   Aether Catalog definitions — MachineLearning_CommittedPCPThreeColoringZK
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CommittedPCPThreeColoringZK`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CommittedPCPThreeColoringZK.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

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

namespace MachineLearning.CommittedPCPThreeColoringZK

open Finset MachineLearning.CommittedLocalOracleZK

/-! ## Sharp 2-transitivity of the colour symmetry group -/






/-! ## The committed 2-query PCP for 3-colouring -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A proper 3-colouring of the edge set `E`. -/
def IsProper (E : Finset (V × V)) (c : V → ZMod 3) : Prop := ∀ e ∈ E, c e.1 ≠ c e.2

/-- The verifier's randomness: a uniformly chosen edge. -/
abbrev Edge (E : Finset (V × V)) := {e : V × V // e ∈ E}

/-- The two coordinates queried on the challenged edge. -/
def queries (E : Finset (V × V)) (r : Edge E) : Finset V := {r.1.1, r.1.2}

omit [Fintype V] in
theorem queries_card_le_two (E : Finset (V × V)) (r : Edge E) : (queries E r).card ≤ 2 :=
  le_trans (card_insert_le _ _) (by simp)

/-- The simulator's randomness: an ordered pair of **distinct** colours. -/
abbrev SimRand := {q : ZMod 3 × ZMod 3 // q.1 ≠ q.2}

instance : Nonempty (SimRand) := ⟨⟨(0, 1), by decide⟩⟩

/-- The committed local-oracle protocol: the randomized colouring `π ∘ c`,
committed with a coordinate-wise one-time pad and opened on the challenged
edge. -/
def zkOracle (E : Finset (V × V)) (c : V → ZMod 3) :
    CommittedOracle V (ZMod 3) (V → ZMod 3) (V → Option (ZMod 3)) (V → ZMod 3)
      (Edge E) (Equiv.Perm (ZMod 3)) :=
  otpOracle (fun π v => π (c v)) (queries E) 2 (queries_card_le_two E)

/-- **The simulator.** It never inspects the colouring `c`: on the challenged
edge it writes down a uniformly random ordered pair of distinct colours. -/
def zkSim (E : Finset (V × V)) (r : Edge E) (s : SimRand) : V → ZMod 3 :=
  fun w => if w = r.1.1 then s.1.1 else if w = r.1.2 then s.1.2 else 0







end MachineLearning.CommittedPCPThreeColoringZK


