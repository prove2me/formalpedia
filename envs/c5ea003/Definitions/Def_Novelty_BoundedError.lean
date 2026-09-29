-- Prove2me | Definitions.Def_Novelty_BoundedError
-- name    : Novelty_BoundedError
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:09.176804+00:00
-- url     : https://prove2.me/theorems/41ce6165-eb0d-4516-b46a-72b1e6d735f3
-- title:
--   Aether Catalog definitions — Novelty_BoundedError
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BoundedError`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BoundedError.lean by skeleton subtraction
import Mathlib
/-
# Bounded-error surveillance and the sharp rate–distortion law

This file deepens the information-theoretic study of surveillance on finite
dynamic networks.  An observer watches a network whose instantaneous
configuration ranges over a finite state space `S`.  It records a measurement in
an alphabet `M` through a channel `obs : S → M` and later reconstructs the
configuration with a decoder `dec : M → S`.  The **rate** of a channel is the
number of distinct records it can emit.

We prove two families of results that go beyond the exact-reconstruction regime.

## 1. A combinatorial Fano bound (bounded-error surveillance)

The set of configurations the observer reconstructs correctly has size at most
the rate (`reconSet_card_le_rate`).  Consequently the number of *misreconstructed*
configurations is at least `|S| - rate` (`fano_error_bound`), so to keep the
number of errors within a budget `k` the observer must collect rate at least
`|S| - k` (`bounded_error_rate_lower`), i.e. at least `log₂ (|S| - k)` bits
(`bounded_error_bits`).  In particular a *perfectly private* observer
(rate `= 1`) misreconstructs all but one configuration
(`privacy_error_bound`): perfect privacy and low-error surveillance are
quantitatively incompatible.

## 2. A sharp rate–distortion law

Fix a dissimilarity `d : S → S → ℕ` and a distortion budget `D`.  A channel/decoder
pair *achieves distortion `D`* when every configuration is reconstructed within
`D`.  We show:

* every achieving pair induces a `D`-cover of the state space by the decoded
  records, of size at most the rate (`achieves_gives_cover`);
* conversely, every `D`-cover is realised by an explicit channel of rate at most
  the cover size (`cover_achieves_rate`).

Combining the two, the minimum achievable surveillance rate equals the
`D`-covering number of the network (`rate_distortion_sharp`): the privacy–utility
tradeoff *is* a covering problem, and the bound is tight.
-/

open Function Finset

namespace SurveillanceBoundedError

variable {S M : Type*} [Fintype S] [Fintype M] [DecidableEq S] [DecidableEq M]

/-- The **rate** of a channel: the number of distinct records it can emit. -/
def rate (obs : S → M) : ℕ := (Finset.univ.image obs).card

/-- The channel reveals nothing: every configuration yields the same record. -/
def PerfectPrivacy (obs : S → M) : Prop := ∀ s t, obs s = obs t

/-- The set of configurations the observer reconstructs correctly. -/
def reconSet (obs : S → M) (dec : M → S) : Finset S :=
  Finset.univ.filter (fun s => dec (obs s) = s)

/-- The set of configurations the observer misreconstructs. -/
def errSet (obs : S → M) (dec : M → S) : Finset S :=
  Finset.univ.filter (fun s => dec (obs s) ≠ s)

/-! ### 1. The combinatorial Fano bound -/








/-! ### 2. The sharp rate–distortion law -/

/-- `C` is a `D`-cover: every configuration lies within distortion `D` of some
center in `C`. -/
def IsDCover (d : S → S → ℕ) (D : ℕ) (C : Finset S) : Prop :=
  ∀ s, ∃ c ∈ C, d c s ≤ D

/-- The pair `(obs, dec)` reconstructs every configuration to within distortion
`D`. -/
def AchievesDistortion (obs : S → M) (dec : M → S) (d : S → S → ℕ) (D : ℕ) : Prop :=
  ∀ s, d (dec (obs s)) s ≤ D



/-- The **`D`-covering number** of the network: the least size of a `D`-cover. -/
noncomputable def minCover (d : S → S → ℕ) (D : ℕ) : ℕ :=
  sInf {n | ∃ C : Finset S, IsDCover d D C ∧ C.card = n}




/-! ### Concrete instantiation: directed social networks on `n` nodes -/



end SurveillanceBoundedError


