-- Prove2me | solution 1 for Cryptography.BerggrenModular.applyWord_ne_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:21:22.163541+00:00
-- url     : https://prove2.me/submissions/acd3fb9a-3925-48c2-997a-590daddab608

-- Sol generated from Cryptography/BerggrenModular/Hardness.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_cons
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_valid
import Theorems.Thm_Cryptography_BerggrenModular_hyp_le_applyWord
import Theorems.Thm_Cryptography_BerggrenModular_hyp_lt_applyMove
import Theorems.Thm_Cryptography_BerggrenModular_root_valid

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







/-! ## The `B₂` discrete logarithm -/







/-! ## The separation -/



open Cryptography.BerggrenModular in
theorem solution{u : List Move} (hu : u ≠ []) : applyWord u root ≠ root := by
  match u with
  | [] => exact absurd rfl hu
  | i :: rest =>
      have h1 : root.2.2 ≤ (applyWord rest root).2.2 := hyp_le_applyWord rest root_valid
      have h2 : (applyWord rest root).2.2 < (applyMove i (applyWord rest root)).2.2 :=
        hyp_lt_applyMove (applyWord_valid rest root_valid)
      intro hEq
      have : (applyWord (i :: rest) root).2.2 = root.2.2 := by rw [hEq]
      rw [applyWord_cons] at this
      linarith
