-- Prove2me | solution 1 for MachineLearning.CommittedPCPThreeColoringZK.zkSim_perfectly_simulates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:18:29.755644+00:00
-- url     : https://prove2.me/submissions/6ade4040-2225-4b3b-991c-446a23de898b

-- Sol generated from MachineLearning/CommittedPCPThreeColoringZK.lean
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK
import Definitions.Def_MachineLearning_CommittedPCPThreeColoringZK
import Theorems.Thm_MachineLearning_CommittedLocalOracleZK_perfectlySimulates_of_bijection
import Theorems.Thm_MachineLearning_CommittedLocalOracleZK_restrictTo_eq_iff
import Theorems.Thm_MachineLearning_CommittedPCPThreeColoringZK_perm3_exists

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

/-- In a 3-element alphabet, the element distinct from two given distinct
elements is unique (a finite check on 81 cases). -/
theorem fin3_third_unique :
    ∀ a b u v : Fin 3, a ≠ b → u ≠ a → u ≠ b → v ≠ a → v ≠ b → u = v := by decide

/-- The same statement for the colour alphabet `ZMod 3`. -/
theorem zmod3_third_unique :
    ∀ a b u v : ZMod 3, a ≠ b → u ≠ a → u ≠ b → v ≠ a → v ≠ b → u = v := fin3_third_unique


/-- **Uniqueness half of sharp 2-transitivity**: a permutation of a 3-element
alphabet is determined by its values at two distinct points. -/
theorem perm3_unique (x y a b : ZMod 3) (hab : a ≠ b)
    (π σ : Equiv.Perm (ZMod 3)) (hπx : π x = a) (hπy : π y = b)
    (hσx : σ x = a) (hσy : σ y = b) : π = σ := by
  refine Equiv.ext fun z => ?_
  by_cases hzx : z = x
  · rw [hzx, hπx, hσx]
  by_cases hzy : z = y
  · rw [hzy, hπy, hσy]
  have h1 : π z ≠ a := by rw [← hπx]; exact fun h => hzx (π.injective h)
  have h2 : π z ≠ b := by rw [← hπy]; exact fun h => hzy (π.injective h)
  have h3 : σ z ≠ a := by rw [← hσx]; exact fun h => hzx (σ.injective h)
  have h4 : σ z ≠ b := by rw [← hσy]; exact fun h => hzy (σ.injective h)
  exact zmod3_third_unique a b (π z) (σ z) hab h1 h2 h3 h4


/-! ## The committed 2-query PCP for 3-colouring -/

variable {V : Type*} [Fintype V] [DecidableEq V]






instance : Nonempty (SimRand) := ⟨⟨(0, 1), by decide⟩⟩










open MachineLearning.CommittedPCPThreeColoringZK in
theorem solution{E : Finset (V × V)} {c : V → ZMod 3}
    (hc : IsProper E c) :
    PerfectlySimulatesOpened (Rc := V → ZMod 3) (zkOracle E c) (zkSim E) := by
  -- the colour pair opened on the challenged edge, as a bijection from the
  -- prover's randomness (colour permutations) to the simulator's (distinct pairs)
  refine perfectlySimulates_of_bijection
    (fun r π => ⟨(π (c r.1.1), π (c r.1.2)), fun h => hc r.1 r.2 (π.injective h)⟩) ?_ ?_
  · intro r
    have hcxy : c r.1.1 ≠ c r.1.2 := hc r.1 r.2
    constructor
    · intro π σ h
      have h1 : π (c r.1.1) = σ (c r.1.1) := congrArg (fun q : SimRand => q.1.1) h
      have h2 : π (c r.1.2) = σ (c r.1.2) := congrArg (fun q : SimRand => q.1.2) h
      have hab : π (c r.1.1) ≠ π (c r.1.2) := fun hh => hcxy (π.injective hh)
      exact perm3_unique (c r.1.1) (c r.1.2) (π (c r.1.1)) (π (c r.1.2)) hab π σ rfl rfl
        h1.symm h2.symm
    · intro s
      obtain ⟨π, h1, h2⟩ := perm3_exists (c r.1.1) (c r.1.2) s.1.1 s.1.2 hcxy s.2
      exact ⟨π, Subtype.ext (Prod.ext h1 h2)⟩
  · intro r π
    have hcxy : c r.1.1 ≠ c r.1.2 := hc r.1 r.2
    have hxy : r.1.1 ≠ r.1.2 := fun h => hcxy (by rw [h])
    rw [restrictTo_eq_iff]
    intro i hi
    have hi' : i = r.1.1 ∨ i = r.1.2 := by
      simpa [zkOracle, otpOracle, queries] using hi
    rcases hi' with rfl | rfl
    · simp [zkOracle, otpOracle, zkSim]
    · simp [zkOracle, otpOracle, zkSim, hxy.symm]
