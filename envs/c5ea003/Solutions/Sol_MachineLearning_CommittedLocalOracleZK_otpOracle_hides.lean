-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.otpOracle_hides
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:07:27.295945+00:00
-- url     : https://prove2.me/submissions/689479ee-b176-4ef6-864f-a387bb285270

-- Sol generated from MachineLearning/CommittedLocalOracleZK.lean
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

/-!
# Committed local-oracle protocols: composing PCP locality with commitment hiding

A *committed local-oracle protocol* is the standard "PCP + commitment" compiler:

* the prover holds a (randomized) proof string `proof p : I → A` indexed by the
  coordinate set `I` over an alphabet `A`;
* it commits to the whole string with commitment randomness `ρ : Rc`, producing a
  commitment message `com (proof p) ρ : C`;
* the honest verifier tosses coins `r : Rv` and queries the **constant-size** set
  of coordinates `Q r` (`(Q r).card ≤ qbound`);
* the prover answers by revealing the queried symbols together with the opening
  data `openInfo (proof p) ρ (Q r) : O`.

The resulting *transcript* is
`(commitment, verifier coins, opened symbols, opening data)`,
where the "opened symbols" are recorded as the partial function
`restrictTo (Q r) (proof p) : I → Option A`, which is `none` off the query set —
so the transcript literally contains no information about unopened coordinates
beyond what the commitment and the openings carry.

## Main result

`perfect_hvzk` : if the commitment scheme

* **perfectly hides unopened coordinates** (`PerfectlyHidesUnopened`): for any two
  strings agreeing on a set `T` there is a bijection of the commitment randomness
  carrying the commitment *and the openings on `T`* of one to those of the other;
* and the local view of the queried symbols is **perfectly simulatable**
  (`PerfectlySimulatesOpened`): for every fixing of the verifier's coins the
  distribution of the opened symbols is reproduced exactly by a simulator that
  does not see the witness,

then the *full* transcript distribution of the real constant-query interaction
equals the simulator's transcript distribution exactly: the protocol is
**perfect honest-verifier zero knowledge**.

The proof is a genuine two-level distributional argument: the hiding hypothesis
shows that the number of commitment randomnesses consistent with a given
(commitment, opening) pair depends on the message *only through its restriction
to the opened set* (`fiberCount_congr`), and the local-simulation hypothesis then
matches the two counting measures fibre by fibre (`realCount_mul_card_sim`).

We also supply a nontrivial instance: the coordinate-wise one-time-pad
commitment over an arbitrary finite abelian group perfectly hides unopened
coordinates (`otpOracle_hides`), while opening a coordinate genuinely reveals the
pad there, so the openings are a real part of the transcript.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "hiding of the unopened part" and "simulatability of
the opened part" are *independent* resources, and their composition should be
exact (not merely statistical), because the transcript factorizes over the fibres
of the restriction map `u ↦ u|_{Q r}`.

Experiment (Experimenter): formalized both resources as finite counting
statements (no measure theory needed), and reduced the transcript count to
`∑_p [proof p |_{Q r} = t] · fiberCount (proof p)` (`realCount_eq_sum`). The
hiding hypothesis makes `fiberCount` constant on a fibre; the simulation
hypothesis equates fibre sizes after cross-multiplying by the two
randomness-space cardinalities.

Analysis (Analyst): the cross-multiplied form of `PerfectlySimulatesOpened` is
essential — dividing by `|P|`, `|S|` inside ℕ would be lossy, and the ℚ-valued
statement follows at the end in one step. A subtle corner case is the *empty
fibre*: there we must transport emptiness across the hypothesis, which needs
`0 < |P|` (`Nonempty P`). Note the commitment- and verifier-randomness spaces are
*not* assumed nonempty: if either is empty both distributions are identically
zero and the theorem still holds (the `div` convention `x/0 = 0` is used).

Critique (Critic): hiding is stated as an explicit bijection of the randomness
space rather than as equality of pushforward measures. These are equivalent for
finite randomness spaces up to the counting lemma proved here
(`fiberCount_congr`), and the bijection form is what every perfectly hiding
scheme actually provides — witness the one-time-pad instance, which is proved,
not assumed.

Synthesis (PI): perfect HVZK of the compiled protocol is a *composition theorem*:
hiding controls the vertical (commitment) direction, simulation the horizontal
(opened symbols) direction, and constant query complexity is what makes the
horizontal direction small enough to simulate at all.
-- !-- Lab Notes -- !--
-/

open MachineLearning.CommittedLocalOracleZK

open Finset

variable {I A C O Rc Rv P S : Type*}





variable [DecidableEq I]






variable [Fintype I] [Fintype Rc] [Fintype Rv] [Fintype P] [Fintype S]
variable [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]

















/-! ## An instance: the coordinate-wise one-time-pad commitment

Over a finite abelian group `A`, commit to `u : I → A` with a uniformly random pad
`ρ : I → A` by sending `u + ρ`, and open a coordinate by revealing the pad there.
This perfectly hides every unopened coordinate, *even given* the openings of the
queried ones. -/


variable [AddCommGroup A]





open MachineLearning.CommittedLocalOracleZK in
theorem solution(w : P → I → A) (Q : Rv → Finset I) (qb : ℕ)
    (hq : ∀ r, (Q r).card ≤ qb) :
    PerfectlyHidesUnopened (Rc := I → A) (otpOracle w Q qb hq) := by
  intro T u v huv
  refine ⟨Equiv.addRight (fun i => u i - v i), fun ρ => ⟨?_, ?_⟩⟩
  · funext i
    show u i + ρ i = v i + (ρ + fun i => u i - v i) i
    simp only [Pi.add_apply]
    abel
  · funext i
    by_cases hi : i ∈ T
    · show (if i ∈ T then some (ρ i) else none)
        = if i ∈ T then some ((ρ + fun i => u i - v i) i) else none
      simp only [if_pos hi, Pi.add_apply, huv i hi, sub_self, add_zero]
    · show (if i ∈ T then some (ρ i) else none)
        = if i ∈ T then some ((ρ + fun i => u i - v i) i) else none
      simp only [if_neg hi]
