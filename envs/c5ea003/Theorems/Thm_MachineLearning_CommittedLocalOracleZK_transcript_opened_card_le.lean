-- Prove2me | Theorems.Thm_MachineLearning_CommittedLocalOracleZK_transcript_opened_card_le
-- name    : MachineLearning.CommittedLocalOracleZK.transcript_opened_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:42:52.149331+00:00
-- url     : https://prove2.me/theorems/a95fe4b1-3985-40eb-9e63-4f5180077be7
-- title:
--   Constant-query locality of the transcript.
-- statement:
--   **Constant-query locality of the transcript.** At most `qbound` symbols of the
--   proof string appear in a transcript, no matter how long the proof string is.
--
--   ```lean
--   theorem MachineLearning.CommittedLocalOracleZK.transcript_opened_card_le[Fintype I] (Pr : CommittedOracle I A C O Rc Rv P)
--       (p : P) (r : Rv) :
--       (univ.filter fun i => (restrictTo (Pr.Q r) (Pr.proof p) i).isSome).card ≤ Pr.qbound := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CommittedLocalOracleZK.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CommittedLocalOracleZK.lean#L152

-- Thm stub generated from MachineLearning/CommittedLocalOracleZK.lean
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

theorem MachineLearning.CommittedLocalOracleZK.transcript_opened_card_le[Fintype I] (Pr : CommittedOracle I A C O Rc Rv P)
    (p : P) (r : Rv) :
    (univ.filter fun i => (restrictTo (Pr.Q r) (Pr.proof p) i).isSome).card ≤ Pr.qbound := by sorry
