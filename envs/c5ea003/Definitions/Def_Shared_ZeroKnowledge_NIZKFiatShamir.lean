-- Prove2me | Definitions.Def_Shared_ZeroKnowledge_NIZKFiatShamir
-- name    : Shared_ZeroKnowledge_NIZKFiatShamir
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:16:15.791906+00:00
-- url     : https://prove2.me/theorems/7589e417-b912-4e24-be9e-8bdb3c16e004
-- title:
--   Aether Catalog definitions — Shared_ZeroKnowledge_NIZKFiatShamir
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ZeroKnowledge.NIZKFiatShamir`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ZeroKnowledge/NIZKFiatShamir.lean by skeleton subtraction
import Mathlib

/-!
# Non-interactive zero knowledge: the Fiat–Shamir transform in the random-oracle model

An interactive `Σ`-protocol (commit `a`, random challenge `c`, response `r`) is made
*non-interactive* by replacing the verifier's coin flips with the value `H a` of a hash
function. In the random-oracle model the hash function is drawn uniformly from the finite
set of *all* functions `Msg → Chal`, and this file carries out the resulting exact
counting.

## Main results

* `fiber_card_const` — for a fixed query `a`, all the fibers `{H | H a = c}` have the same
  size. Equivalently: *the value of a random oracle at a point is uniformly distributed*,
  and reprogramming the oracle at one point is undetectable — the counting fact behind
  zero knowledge of the transformed protocol.
* `fiber_prob` — the probability that a uniform oracle sends `a` to a fixed challenge is
  exactly `1/|Chal|`.
* `hashHits_card_mul` and `fsError_eq` — the probability that `H a` lands in a set `B` of
  bad challenges is exactly `|B|/|Chal|`, i.e. Fiat–Shamir with a single fixed first
  message inherits the soundness error of the interactive protocol.
* `fs_union_bound` — a cheating prover that may try any first message from a set `A₀`
  succeeds with probability at most `|A₀| · d / |Chal|`, where `d` bounds the number of
  answerable challenges.
* `SigmaProtocol.fiat_shamir_soundness` — the same statement for a `d`-special-sound
  `Σ`-protocol on a false statement: the non-interactive proof system is sound with error
  `|A₀| · d / |Chal|`.
-/

open Finset

namespace ZKFiatShamir

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-! ## Random oracles: exact fiber counting -/

/-- The set of oracles sending the query `a` to the answer `c`. -/
def fiber (a : A) (c : C) : Finset (A → C) := univ.filter fun H => H a = c





/-! ## Soundness of the Fiat–Shamir transform -/

/-- The oracles whose answer on `a` lies in the "bad" set `B`. -/
def hashHits (a : A) (B : Finset C) : Finset (A → C) := univ.filter fun H => H a ∈ B


/-- The soundness error of the Fiat–Shamir transform for a single first message `a`:
the fraction of oracles that hand the prover a bad challenge. -/
noncomputable def fsError (a : A) (B : Finset C) : ℝ :=
  ((hashHits a B).card : ℝ) / Fintype.card (A → C)




/-! ## Application to `Σ`-protocols -/

/-- A three-move public-coin proof system: on statement `x` the prover sends a first
message `a`, receives a challenge `c` and answers with `r`. -/
structure SigmaProtocol (Stmt Msg Chal Resp : Type*) where
  /-- The verifier's decision predicate. -/
  verify : Stmt → Msg → Chal → Resp → Bool

variable {Stmt Msg Resp : Type*}

/-- The challenges that a (possibly cheating) prover can answer after having committed to
the first message `a`. -/
def SigmaProtocol.answerable [Fintype Resp] (P : SigmaProtocol Stmt Msg C Resp)
    (x : Stmt) (a : Msg) : Finset C :=
  univ.filter fun c => ∃ r, P.verify x a c r

/-- `d`-special soundness relative to a set of false statements: after any first message,
at most `d` of the challenges admit a valid response. (For Schnorr-like protocols
`d = 1`.) -/
def SigmaProtocol.SpecialSound [Fintype Resp] (P : SigmaProtocol Stmt Msg C Resp)
    (bad : Stmt → Prop) (d : ℕ) : Prop :=
  ∀ x, bad x → ∀ a, (P.answerable x a).card ≤ d



end ZKFiatShamir


