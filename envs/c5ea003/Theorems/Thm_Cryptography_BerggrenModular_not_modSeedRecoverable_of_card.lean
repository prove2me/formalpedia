-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_not_modSeedRecoverable_of_card
-- name    : Cryptography.BerggrenModular.not_modSeedRecoverable_of_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:39:04.735246+00:00
-- url     : https://prove2.me/theorems/9a64667e-87e8-4e50-81bc-ad42dbd8ffc2
-- title:
--   Information-theoretic impossibility.
-- statement:
--   **Information-theoretic impossibility.**  Once `m³ < 3^k`, no function of the
--   observed modular state can return the control word.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.not_modSeedRecoverable_of_card(m k : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ k) :
--       ¬ ModSeedRecoverable m k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/Hardness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/Hardness.lean#L145

-- Thm stub generated from Cryptography/BerggrenModular/Hardness.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Hardness
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

open Cryptography
open BerggrenModular

/-! ## Integer seed recovery is easy -/





/-! ## The modular observation -/




/-! ## Counting: `3^k` control words versus `m³` states -/

theorem Cryptography.BerggrenModular.not_modSeedRecoverable_of_card(m k : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ k) :
    ¬ ModSeedRecoverable m k := by sorry
