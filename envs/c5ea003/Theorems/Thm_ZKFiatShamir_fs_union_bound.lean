-- Prove2me | Theorems.Thm_ZKFiatShamir_fs_union_bound
-- name    : ZKFiatShamir.fs_union_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:53:43.886988+00:00
-- url     : https://prove2.me/theorems/b09f121e-0791-4adb-a3f2-70f3ca7b063f
-- title:
--   Union bound over the prover's choice of first message: a cheating prover that is
-- statement:
--   **Union bound over the prover's choice of first message**: a cheating prover that is
--   allowed to grind through all first messages in `Aâ` fools the non-interactive verifier for
--   at most a `|Aâ| Â· d / |Chal|` fraction of oracles.
--
--   ```lean
--   theorem ZKFiatShamir.fs_union_bound[Nonempty C] (A₀ : Finset A) (bad : A → Finset C) (d : ℕ)
--       (hd : ∀ a, (bad a).card ≤ d) :
--       ((univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card : ℝ) / Fintype.card (A → C)
--         ≤ (A₀.card : ℝ) * d / Fintype.card C := by sorry
--   /-! ## Application to `Σ`-protocols -/
--
--
--   variable {Stmt Msg Resp : Type*}
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ZeroKnowledge/NIZKFiatShamir.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ZeroKnowledge/NIZKFiatShamir.lean#L124

-- Thm stub generated from Shared/ZeroKnowledge/NIZKFiatShamir.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_NIZKFiatShamir

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

open ZKFiatShamir

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-! ## Random oracles: exact fiber counting -/






/-! ## Soundness of the Fiat–Shamir transform -/

theorem ZKFiatShamir.fs_union_bound[Nonempty C] (A₀ : Finset A) (bad : A → Finset C) (d : ℕ)
    (hd : ∀ a, (bad a).card ≤ d) :
    ((univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card : ℝ) / Fintype.card (A → C)
      ≤ (A₀.card : ℝ) * d / Fintype.card C := by sorry
