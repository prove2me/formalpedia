-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_Hardness
-- name    : Cryptography_BerggrenModular_Hardness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:06:25.36471+00:00
-- url     : https://prove2.me/theorems/fff5c7a8-f8bd-4c8e-95fb-c6d1610fb310
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_Hardness
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.Hardness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/Hardness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular

/-!
# Seed recovery: easy over `ℤ`, information-theoretically hard over `ℤ/m`

Fix the Berggren root `(3,4,5)` and a *control word* `u ∈ {B₁,B₂,B₃}^k`.  The
*seed-recovery problem* asks: from the single observed state `applyWord u root`,
reconstruct `u`.

* Over `ℤ` this is **easy**: `recoverFrom` solves it with `k` comparisons and `k`
  linear maps (`intSeedRecoverable`).  This is a corollary of the exactness of the
  classifier `whichMove` together with the freeness of the Berggren monoid.

* Over `ℤ/m` the same problem becomes **impossible** once `k` is large compared to
  the modulus, and quantitatively ambiguous long before that:

  - `mod_ambiguity_lower_bound` : for every `n` with `m³·n < 3^k` there is an
    observed modular state with more than `n` consistent control words.  Taking
    `n = ⌈3^k/m³⌉ − 1` this is the promised `Ω(3^k / poly(m))` bound: the
    modulus is polynomial-size, the ambiguity is exponential.
  - `not_modSeedRecoverable_of_card` : if `m³ < 3^k` no recovery function exists.
  - `not_modSeedRecoverable_of_dl` : recovery for *all* words of length `≤ k`
    would in particular solve the discrete-logarithm problem for the matrix `B₂`
    modulo `m`; and that problem is already unsolvable for `k ≥ m³` because the
    `B₂`-orbit has collided by then.  This is the precise sense of
    "hard unless the `B₂` discrete logarithm mod `m` is easy".

## Main results

* `intSeedRecoverable`
* `mod_ambiguity_lower_bound`
* `not_modSeedRecoverable_of_card`
* `dlEasy_of_modSeedRecoverable`
* `not_dlEasy_of_large`
* `berggren_modulus_separation` — the combined statement.
-/

namespace Cryptography
namespace BerggrenModular

/-! ## Integer seed recovery is easy -/


/-- Self-terminating integer seed recovery: peel moves until the root is reached. -/
def recoverFrom : ℕ → Tri → List Move
  | 0, _ => []
  | n + 1, v =>
      if v = root then []
      else whichMove v :: recoverFrom n (invMove (whichMove v) v)



/-! ## The modular observation -/

/-- The modular state observed after running the control word `u` from the root. -/
def stateMod (m : ℕ) (u : List Move) : TriM m := redTri m (applyWord u root)

/-- Seed recovery modulo `m`, for control words of length at most `k`. -/
def ModSeedRecoverable (m k : ℕ) : Prop :=
  ∃ f : TriM m → List Move, ∀ u : List Move, u.length ≤ k → f (stateMod m u) = u


/-! ## Counting: `3^k` control words versus `m³` states -/

/-- The control words of length `k`, as functions. -/
def stateModF (m k : ℕ) (u : Fin k → Move) : TriM m := stateMod m (List.ofFn u)






/-! ## The `B₂` discrete logarithm -/

/-- The discrete-logarithm-like problem for the Berggren matrix `B₂` modulo `m`:
given the state reached by `t` applications of `B₂`, return `t`.  By
`vecOfM_iterate_applyMoveM` this state is exactly `B₂^t · (3,4,5)ᵀ` over `ℤ/m`. -/
def DLEasy (m k : ℕ) : Prop :=
  ∃ g : TriM m → ℕ, ∀ t ≤ k, g (stateMod m (List.replicate t Move.m2)) = t






/-! ## The separation -/


end BerggrenModular
end Cryptography


