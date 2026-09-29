-- Prove2me | Definitions.Def_MachineLearning_CommittedLocalOracleZK
-- name    : MachineLearning_CommittedLocalOracleZK
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:19.363739+00:00
-- url     : https://prove2.me/theorems/97039e97-fe0c-49f6-bb94-40dee42238f8
-- title:
--   Aether Catalog definitions — MachineLearning_CommittedLocalOracleZK
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CommittedLocalOracleZK`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CommittedLocalOracleZK.lean by skeleton subtraction
import Mathlib

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

namespace MachineLearning.CommittedLocalOracleZK

open Finset

variable {I A C O Rc Rv P S : Type*}

/-- The partial view of a proof string obtained by opening exactly the
coordinates in `T`: `none` outside `T`. -/
def restrictTo [DecidableEq I] (T : Finset I) (f : I → A) : I → Option A :=
  fun i => if i ∈ T then some (f i) else none



/-- A **committed local-oracle protocol**: a commitment scheme (`com`, `openInfo`)
applied to a randomized proof string (`proof`), queried at the constant-size
coordinate sets `Q r` chosen by the verifier's coins. -/
structure CommittedOracle (I A C O Rc Rv P : Type*) [DecidableEq I] where
  /-- The commitment message sent by the prover. -/
  com : (I → A) → Rc → C
  /-- The opening data revealed for the queried set. -/
  openInfo : (I → A) → Rc → Finset I → O
  /-- The coordinates queried on verifier randomness `r`. -/
  Q : Rv → Finset I
  /-- The query-complexity bound. -/
  qbound : ℕ
  /-- Constant query complexity. -/
  query_card_le : ∀ r, (Q r).card ≤ qbound
  /-- The prover's randomized proof string. -/
  proof : P → I → A

variable [DecidableEq I]

/-- The transcript of one execution: commitment, verifier coins, opened symbols
(as a partial assignment), and opening data. -/
abbrev Transcript (I A C O Rv : Type*) := C × Rv × (I → Option A) × O

/-- The honest transcript produced on prover randomness `p`, commitment
randomness `ρ` and verifier coins `r`. -/
def realTranscript (Pr : CommittedOracle I A C O Rc Rv P) (p : P) (ρ : Rc) (r : Rv) :
    Transcript I A C O Rv :=
  (Pr.com (Pr.proof p) ρ, r, restrictTo (Pr.Q r) (Pr.proof p),
    Pr.openInfo (Pr.proof p) ρ (Pr.Q r))

/-- The transcript produced by a simulator which, on coins `r` and its own
randomness `s`, invents a local assignment `sim r s` and honestly commits to and
opens it. -/
def simTranscript (Pr : CommittedOracle I A C O Rc Rv P) (sim : Rv → S → I → A)
    (s : S) (ρ : Rc) (r : Rv) : Transcript I A C O Rv :=
  (Pr.com (sim r s) ρ, r, restrictTo (Pr.Q r) (sim r s), Pr.openInfo (sim r s) ρ (Pr.Q r))


section Counting

variable [Fintype I] [Fintype Rc] [Fintype Rv] [Fintype P] [Fintype S]
variable [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]

/-- Number of commitment randomnesses consistent with a given commitment `c` and
opening data `o` for the message `u` opened on `T`. -/
def fiberCount (Pr : CommittedOracle I A C O Rc Rv P) (u : I → A) (T : Finset I)
    (c : C) (o : O) : ℕ :=
  (univ.filter fun ρ => Pr.com u ρ = c ∧ Pr.openInfo u ρ T = o).card

/-- **Perfect hiding of unopened coordinates.** If two proof strings agree on the
opened set `T`, a bijection of the commitment randomness carries the commitment
*and* the opening data on `T` of the first to those of the second. -/
def PerfectlyHidesUnopened (Pr : CommittedOracle I A C O Rc Rv P) : Prop :=
  ∀ (T : Finset I) (u v : I → A), (∀ i ∈ T, u i = v i) →
    ∃ e : Rc ≃ Rc, ∀ ρ, Pr.com u ρ = Pr.com v (e ρ) ∧
      Pr.openInfo u ρ T = Pr.openInfo v (e ρ) T

/-- **Perfect simulation of the opened coordinates.** For every fixing of the
verifier's coins, the distribution of the opened symbols under the prover's
randomness is exactly reproduced by the simulator (stated by cross-multiplying
the two uniform distributions, so as to stay inside ℕ). -/
def PerfectlySimulatesOpened (Pr : CommittedOracle I A C O Rc Rv P)
    (sim : Rv → S → I → A) : Prop :=
  ∀ (r : Rv) (t : I → Option A),
    (univ.filter fun p : P => restrictTo (Pr.Q r) (Pr.proof p) = t).card * Fintype.card S
      = (univ.filter fun s : S => restrictTo (Pr.Q r) (sim r s) = t).card * Fintype.card P


/-- Number of random executions producing a given transcript, in the real
interaction. -/
def realCount (Pr : CommittedOracle I A C O Rc Rv P) (τ : Transcript I A C O Rv) : ℕ :=
  (univ.filter fun x : P × Rc × Rv => realTranscript Pr x.1 x.2.1 x.2.2 = τ).card

/-- Number of random executions producing a given transcript, in the simulation. -/
def simCount (Pr : CommittedOracle I A C O Rc Rv P) (sim : Rv → S → I → A)
    (τ : Transcript I A C O Rv) : ℕ :=
  (univ.filter fun x : S × Rc × Rv => simTranscript Pr sim x.1 x.2.1 x.2.2 = τ).card

/-- The real transcript distribution (uniform prover, commitment and verifier
randomness). -/
def realProb (Pr : CommittedOracle I A C O Rc Rv P) (τ : Transcript I A C O Rv) : ℚ :=
  (realCount Pr τ : ℚ) / (Fintype.card P * Fintype.card Rc * Fintype.card Rv)

/-- The simulated transcript distribution. -/
def simProb (Pr : CommittedOracle I A C O Rc Rv P) (sim : Rv → S → I → A)
    (τ : Transcript I A C O Rv) : ℚ :=
  (simCount Pr sim τ : ℚ) / (Fintype.card S * Fintype.card Rc * Fintype.card Rv)








end Counting

/-! ## An instance: the coordinate-wise one-time-pad commitment

Over a finite abelian group `A`, commit to `u : I → A` with a uniformly random pad
`ρ : I → A` by sending `u + ρ`, and open a coordinate by revealing the pad there.
This perfectly hides every unopened coordinate, *even given* the openings of the
queried ones. -/

section OTP

variable [AddCommGroup A]

/-- The one-time-pad committed local-oracle protocol built from a proof-string
family `w : P → I → A` and a constant-size query family `Q`. -/
def otpOracle (w : P → I → A) (Q : Rv → Finset I) (qb : ℕ) (hq : ∀ r, (Q r).card ≤ qb) :
    CommittedOracle I A (I → A) (I → Option A) (I → A) Rv P where
  com u ρ := fun i => u i + ρ i
  openInfo _ ρ T := restrictTo T ρ
  Q := Q
  qbound := qb
  query_card_le := hq
  proof := w


end OTP

end MachineLearning.CommittedLocalOracleZK


