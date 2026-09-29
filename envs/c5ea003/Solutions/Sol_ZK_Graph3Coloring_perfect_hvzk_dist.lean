-- Prove2me | solution 1 for ZK.Graph3Coloring.perfect_hvzk_dist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:49:11.015253+00:00
-- url     : https://prove2.me/submissions/3f812b91-8ed0-4cab-957c-6aad9818dcb8

-- Sol generated from Cryptography/ZeroKnowledge/Graph3ColoringSimulator.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3Coloring
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringSimulator
import Theorems.Thm_ZK_Graph3Coloring_hvzk_bijection
import Theorems.Thm_ZK_Graph3Coloring_map_uniformOfFintype_of_bijective

/-!
# The Simulation Paradigm for the GMW Graph 3-Colouring Proof

This file formalizes the **simulation paradigm** for the Goldreich–Micali–Wigderson
zero-knowledge proof of graph 3-colourability, building directly on
`Cryptography.ZeroKnowledge.Graph3Coloring`.

The zero-knowledge property is expressed as an *equality of probability
distributions* (`PMF`): the distribution of the verifier's real transcript on a
challenged edge is **exactly equal** to the distribution produced by an efficient
simulator that knows nothing about the prover's secret colouring. Because the two
distributions are literally equal (not merely statistically close), this is
*perfect* honest-verifier zero knowledge.

## The two distributions

* `realTranscriptDist a b hab` — the honest prover holds a proper colouring; on a
  challenged edge with (distinct) endpoint colours `a ≠ b`, it samples a uniformly
  random colour permutation `π ∈ S₃` and opens `(π a, π b)`. This is the pushforward
  of the uniform distribution on `S₃` under the view map.
* `simulatorDist` — the simulator samples a uniformly random *distinct ordered
  pair* of colours, with no reference to any colouring.

## Main results

* `map_uniformOfFintype_of_bijective` — a reusable lemma: the pushforward of a
  uniform distribution under a bijection is again uniform.
* `perfect_hvzk_dist` — **the simulation theorem**: `realTranscriptDist a b hab =
  simulatorDist`. The real transcript and the simulated transcript are identically
  distributed.
* `hvzk_colour_independence` — the real transcript distribution does not depend on
  the actual endpoint colours `(a, b)` at all (only that they are distinct): any
  two challenged edges induce the same distribution. This is the operational
  content of "the verifier learns nothing".
* `perfect_hvzk_apply` — the closed-form probability: every distinct opened pair
  appears with probability exactly `1/6`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The GMW 3-colouring protocol is not merely
"simulatable up to negligible error" but *perfectly* simulatable: the real and
simulated transcript distributions are equal as `PMF`s, because the view map
`π ↦ (π a, π b)` is a bijection from `S₃` onto the six distinct ordered pairs.

Experiment (Experimenter): Formalized both distributions as `PMF`. The proof
reduces perfect ZK to the reusable lemma `map_uniformOfFintype_of_bijective`
(pushforward of uniform under a bijection is uniform), instantiated at the
bijection `hvzk_bijection` already proved in `Graph3Coloring`. Colour-independence
then follows purely formally by transitivity through `simulatorDist`.

Analysis (Analyst): The distributional formulation is strictly stronger than the
bijection lemma alone: it upgrades a combinatorial bijection into a statement
about randomized transcripts, which is the actual definition of zero knowledge.
The colour-independence corollary is the crispest possible statement that the
transcript "leaks nothing" — the *same* random variable is produced regardless of
the secret. The "true but hard" boundary avoided here is full malicious-verifier
ZK (needs rewinding); for the honest verifier, perfect equality is attainable and
proved.

Critique (Critic): `perfect_hvzk_dist` is non-vacuous — it genuinely transports a
bijection through `PMF.map` and `tsum`, not a `decide`. The `Nonempty` instance on
distinct pairs is discharged by an explicit witness `(0,1)`, so the simulator
distribution is well-defined. `perfect_hvzk_apply` gives a concrete `1/6`, ruling
out a trivial reading.

Synthesis (PI): Together with completeness and the soundness gap from
`Graph3Coloring`, this file closes the simulation paradigm: a colouring-oblivious
simulator reproduces the honest transcript distribution exactly.
-- !-- Lab Notes -- !--
-/

open ZK.Graph3Coloring

open scoped Classical










theorem solution(a b : Fin 3) (hab : a ≠ b) :
    realTranscriptDist a b hab = simulatorDist := by
  unfold realTranscriptDist simulatorDist
  exact map_uniformOfFintype_of_bijective _ (hvzk_bijection a b hab)
