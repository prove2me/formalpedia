-- Prove2me | Theorems.Thm_SurveillanceNetworks_covering_rate_bound
-- name    : SurveillanceNetworks.covering_rate_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:45.245687+00:00
-- url     : https://prove2.me/theorems/deda04a4-c3df-4c98-9513-ff82c009e129
-- title:
--   Rate–distortion lower bound.
-- statement:
--   **Rate–distortion lower bound.**  Fix a dissimilarity `d` on configurations, a
--   distortion budget `D`, and a bound `B` on the size of every distortion ball
--   `{s | d c s ≤ D}`.  If the observer reconstructs every configuration to within
--   `D`, then the channel must emit at least `|S| / B` distinct records:
--   `|S| ≤ rate · B`.
--
--   ```lean
--   theorem SurveillanceNetworks.covering_rate_bound(obs : S → M) (dec : M → S) (d : S → S → ℕ) (D B : ℕ)
--       (hball : ∀ c : S, (Finset.univ.filter (fun s => d c s ≤ D)).card ≤ B)
--       (hrec : ∀ s, d (dec (obs s)) s ≤ D) :
--       Fintype.card S ≤ rate obs * B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/SurveillanceNetworks/RateDistortion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/SurveillanceNetworks/RateDistortion.lean#L132

-- Thm stub generated from Applications/SurveillanceNetworks/RateDistortion.lean
import Mathlib
import Definitions.Def_Applications_SurveillanceNetworks_RateDistortion
/-
# Information-theoretic limits of surveillance on finite dynamic networks

We model an observer watching a dynamic social network whose instantaneous
configuration ranges over a finite state space `S` (for example, the set of all
adjacency relations the network may exhibit at a given instant).  The observer
records a measurement drawn from an alphabet `M` through an *observation channel*
`obs : S → M`, and later attempts to reconstruct the true configuration with a
*decoder* `dec : M → S`.

Two idealized regimes are of interest:

* **Perfect surveillance** — the channel is injective, so the true configuration
  is always recoverable from the record.
* **Perfect privacy** — the channel is constant, so the record reveals nothing
  about the configuration.

The central results below quantify the privacy–utility tradeoff as a
rate–distortion problem:

* A faithful reconstruction forces the observation alphabet to be at least as
  large as the state space, hence the observer must collect at least
  `log₂ |S|` bits (`recon_bits`).
* Under a distortion budget `D` measured by a dissimilarity `d`, the number of
  distinct measurements the observer must emit — the *rate* — is at least
  `|S| / B`, where `B` bounds the size of any distortion ball
  (`covering_rate_bound`).
* Perfect privacy pins the rate to `1` (`rate_eq_one_of_privacy`); combined with
  the covering bound, a private observer can meet a distortion budget only if a
  single ball already covers the whole network (`privacy_forces_ball_cover`).
* For any non-trivial network (at least two configurations) perfect privacy and
  faithful reconstruction are mutually exclusive (`privacy_no_recon`), and so are
  perfect privacy and perfect surveillance (`privacy_surv_exclusive`).

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  On a finite dynamic network the observer's minimum
collected information and the achievable reconstruction fidelity obey a hard
rate–distortion tradeoff, and the two extreme regimes — perfect privacy and
perfect surveillance — cannot coexist once the network has more than one state.

EXPERIMENT (Experimenter).  Model configurations as a finite type `S`,
observations as `obs : S → M`, reconstruction as `dec : M → S`.  Perfect
reconstruction `dec ∘ obs = id` forces `obs` injective, giving the counting
bound `|S| ≤ |M|` and hence `log₂ |S| ≤ log₂ |M|` bits.  For the distortion
version, partition `S` by the observation fibres: every configuration mapped to a
symbol `m` lies in the distortion ball around `dec m`, so each fibre is bounded by
the ball size `B`, and summing over the used symbols gives `|S| ≤ rate · B`.

ANALYSIS (Analyst).  The fibrewise covering argument is the structural heart: it
converts a channel/decoder pair into a covering of the state space by distortion
balls indexed by the emitted symbols.  Perfect privacy is exactly the degenerate
covering by a single ball, which recovers the impossibility results as the
`rate = 1` corner of the same inequality.

CRITIQUE (Critic).  The impossibility statements are vacuous unless the network
is non-trivial, so every such theorem carries the hypothesis `2 ≤ |S|`, and
`Fintype.exists_pair_of_one_lt_card` supplies the witnessing distinct
configurations.  The existence half `exists_surveillance_iff` shows the counting
bound is tight, ruling out a trivial reading.  No result collapses to `True` or a
pure `decide`.

SYNTHESIS (PI).  A single covering inequality unifies the bit lower bound, the
rate–distortion lower bound, and the privacy/surveillance impossibility, with the
private regime sitting at its `rate = 1` boundary.
-/

open Function Finset

open SurveillanceNetworks

variable {S M : Type*} [Fintype S] [Fintype M] [DecidableEq S] [DecidableEq M]

-- An observation channel is a map `obs : S → M`; a decoder is a map `dec : M → S`.





/-! ### Perfect reconstruction: the fundamental counting bound -/






/-! ### The rate–distortion covering bound -/

omit [Fintype M] [DecidableEq S] in

theorem SurveillanceNetworks.covering_rate_bound(obs : S → M) (dec : M → S) (d : S → S → ℕ) (D B : ℕ)
    (hball : ∀ c : S, (Finset.univ.filter (fun s => d c s ≤ D)).card ≤ B)
    (hrec : ∀ s, d (dec (obs s)) s ≤ D) :
    Fintype.card S ≤ rate obs * B := by sorry
