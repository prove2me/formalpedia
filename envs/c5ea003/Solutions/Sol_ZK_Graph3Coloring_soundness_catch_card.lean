-- Prove2me | solution 1 for ZK.Graph3Coloring.soundness_catch_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:52:48.783521+00:00
-- url     : https://prove2.me/submissions/9184a30c-dc73-490e-acec-4801efd5c1ab

-- Sol generated from Cryptography/ZeroKnowledge/Graph3Coloring.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3Coloring
import Theorems.Thm_ZK_Graph3Coloring_soundness_exists_catch

/-!
# Zero-Knowledge Proof for Graph 3-Colourability

This file formalizes the classical **interactive zero-knowledge proof system for
graph 3-colourability** (Goldreich–Micali–Wigderson). A graph is given by a
finite vertex type `V` and a `Finset` of edges `E : Finset (V × V)`. A 3-colouring
is a map `c : V → Fin 3`; it is *proper* when adjacent vertices get distinct
colours.

The protocol: the prover holds a proper colouring `c`, samples a uniformly random
permutation `π ∈ S₃` of the three colours, and commits to `π ∘ c`. The verifier
challenges a uniformly random edge `(u, v)`; the prover opens the two committed
colours `(π (c u), π (c v))`; the verifier accepts iff they differ.

## Main results

* `completeness` — applying any colour permutation to a proper colouring yields a
  proper colouring, so the honest prover always opens distinct colours.
* `soundness_exists_catch` / `soundness_catch_card` / `soundness_prob` — if the
  committed colouring is not proper, at least one edge "catches" the prover, so a
  random-edge verifier rejects with probability `≥ 1/|E|`.
* `revealedView_distinct` — the opened pair always consists of distinct colours.
* `hvzk_view_injective` and `hvzk_bijection` — **honest-verifier zero knowledge**:
  for a fixed challenged edge with distinct endpoint colours `a ≠ b`, the map
  `π ↦ (π a, π b)` is a bijection from `S₃` onto the ordered pairs of distinct
  colours. Hence the real view is distributed *exactly* like the simulator's
  uniform sample over distinct pairs — independent of the actual colouring.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The GMW 3-colouring protocol is *perfectly* honest-
verifier zero knowledge over `Fin 3`, not merely statistically, because
`|S₃| = 6 = |{(a,b) : a ≠ b}|`.

Experiment (Experimenter): Modelled the commitment as `π ∘ c` and the opened
view as `(π a, π b)`. Verified completeness via injectivity of `π`, soundness via
`push_neg` on the properness predicate, and HVZK via a cardinality/injectivity
argument: an injection between two equal-size finite sets is a bijection.

Analysis (Analyst): Perfect HVZK is special to `n = 3` colours (where the symmetric
group order matches the number of distinct ordered pairs). For `n > 3` the map
`π ↦ (π a, π b)` is no longer surjective onto distinct pairs from a single
permutation orbit; one needs the full uniform commitment, still giving perfect
HVZK but via a different counting argument. The "true but hard" part avoided here
is full (malicious-verifier) zero knowledge, which requires modelling rewinding.

Critique (Critic): The bijection theorem is non-vacuous — it genuinely requires
`a ≠ b` (checked) and uses injectivity plus equal cardinality, not `decide`-only.
Soundness is stated as a strictly positive probability bound, not `True`.

Synthesis (PI): These three pillars (completeness, soundness gap, perfect HVZK)
constitute a complete proof that 3-colourability admits a zero-knowledge proof.
-- !-- Lab Notes -- !--
-/

open ZK.Graph3Coloring

open Finset

variable {V : Type*}


/-! ## Completeness -/


/-! ## Soundness -/




/-! ## Honest-verifier zero knowledge -/






open ZK.Graph3Coloring in
theorem solution(E : Finset (V × V)) (c' : V → Fin 3)
    (h : ¬ IsProperColoring E c') :
    1 ≤ (E.filter (fun e => c' e.1 = c' e.2)).card := by
  obtain ⟨e, heE, hee⟩ := soundness_exists_catch E c' h
  apply Finset.card_pos.mpr
  exact ⟨e, by simp [Finset.mem_filter, heE, hee]⟩
