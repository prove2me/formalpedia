-- Prove2me | solution 1 for Cryptography.BerggrenModular.recoverFrom_correct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:11.687296+00:00
-- url     : https://prove2.me/submissions/000ea2d4-a9e8-4476-8cba-350bd6cfce71

-- Sol generated from Cryptography/BerggrenModular/Hardness.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_cons
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_ne_root
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_valid
import Theorems.Thm_Cryptography_BerggrenModular_invMove_applyMove
import Theorems.Thm_Cryptography_BerggrenModular_root_valid
import Theorems.Thm_Cryptography_BerggrenModular_whichMove_applyMove

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



open Cryptography in
theorem solution: ∀ (n : ℕ) (u : List Move), u.length ≤ n →
    recoverFrom n (applyWord u root) = u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simp only [Nat.le_zero, List.length_eq_zero_iff] at hu
      subst hu; rfl
  | succ n ih =>
      intro u hu
      match u with
      | [] => simp [applyWord, recoverFrom]
      | i :: rest =>
          have hne : applyWord (i :: rest) root ≠ root :=
            applyWord_ne_root (List.cons_ne_nil i rest)
          have hval : Valid (applyWord rest root) := applyWord_valid rest root_valid
          have hlen : rest.length ≤ n := by
            simpa [List.length_cons, Nat.succ_le_succ_iff] using hu
          rw [recoverFrom, if_neg hne, applyWord_cons, whichMove_applyMove i hval,
            invMove_applyMove, ih rest hlen]
