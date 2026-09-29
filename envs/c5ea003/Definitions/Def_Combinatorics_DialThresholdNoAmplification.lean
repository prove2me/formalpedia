-- Prove2me | Definitions.Def_Combinatorics_DialThresholdNoAmplification
-- name    : Combinatorics_DialThresholdNoAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:35:09.491547+00:00
-- url     : https://prove2.me/theorems/5801dbe0-d967-4e60-9399-736cec403d02
-- title:
--   Aether Catalog definitions — Combinatorics_DialThresholdNoAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DialThresholdNoAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DialThresholdNoAmplification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_Round11FingerprintInformation
/-
# DIAL-THRESHOLD: residue dials cannot amplify a Coppersmith hint

Formal companion to `45_DialThreshold_NoAmplification.md` (experiment #380).

**The question.**  A Coppersmith-style attack starts from a *partial key hint*:
the residue `p % m` of the secret prime, with `m ≈ N^{1/4}`.  The "free witness"
side of the programme offers a different kind of data: a vector of **residue
dials** `p ↦ ((D₁ | p), …, (D_K | p))` of Kronecker symbols at fundamental
discriminants.  Each dial is a *periodic* function of `p`, with conductor
dividing `4|D_i|`.  Can the dials *amplify* the hint — cut the candidate set
below what `p % m` already achieves?

**The answer, proved here: no.**  Everything is controlled by one integer,
the conductor lcm `M* = lcm_i cond(D_i)`, measured against the hint modulus `m`:

* `DialThreshold.card_image_dialVec_le` — the **master bound**.  On any candidate
  set inside one hint class mod `m`, the dial vector takes at most
  `M* / gcd(M*, m)` distinct values.  This is the exact amplification budget.
* `DialThreshold.exists_large_dial_fibre` — consequently some dial reading keeps
  at least a `gcd(M*,m)/M*` fraction of the candidates: the dials cannot shrink
  the candidate set by more than the factor `M*/gcd(M*, m)`.
* **Regime 1 (`M* ∣ m`)**: `dialVec_const_of_dvd`, `dial_cut_trivial`,
  `zeroInfo_dialVec_of_dvd`, `zeroInfo_dialVec_postprocessed` — the budget is
  `1`: the dial vector is *constant* on the candidate set, the induced cut is the
  identity, and (in the exact counting sense `Round11.ZeroInfo` of the catalog)
  the dials carry **zero information** about any secret whatsoever, even after
  arbitrary post-processing.
* **Regime 2 (`M* ∤ m`)**: `hint_underdetermines_residue`,
  `not_hintComputable_of_separates`, `pinning_forces_not_dvd`,
  `card_le_of_dialVec_injOn` — a dial system that separates even two candidates
  is *not computable from the hint*, and pinning `C` candidates forces
  `M*/gcd(M*,m) ≥ C`, i.e. the dials must reach strictly beyond the hint.
* `DialThreshold.dial_capacity` — the information-theoretic side: `K` sign dials
  cannot separate more than `3^K` candidates, so pinning needs `K = Ω(log C)`.

Together these are a dichotomy: *hint-computable ⇒ information-useless*
(`no_amplification_of_hintComputable`), *informative ⇒ not hint-computable*.

The concluding section instantiates the two regimes on the experiment's own
numbers with genuine Kronecker dials `(D | ·)`:
`N = 808·10⁶`-scale hint `m = 168` with dials of conductor `12, 84, 168`
(Regime 1) and `N = 340·10⁶`-scale hint `m = 135` with the dial `(-4 | ·)` of
conductor `16` (Regime 2, witnessed by the candidate pair `541, 811`).
-/

namespace DialThreshold

open Finset

/-! ## 1. Residue dials -/

/-- A **residue dial**: an integer-valued statistic of a candidate prime that is
periodic with some conductor.  Kronecker symbols `(D | ·)` at a fixed
discriminant are the motivating example (`DialThreshold.kron`). -/
structure Dial where
  /-- The conductor: the period of the dial. -/
  cond : ℕ
  cond_pos : 0 < cond
  /-- The reading of the dial at a candidate. -/
  chi : ℕ → ℤ
  periodic : ∀ n, chi (n + cond) = chi n

namespace Dial

variable (d : Dial)




end Dial

/-! ### Kronecker dials

The free-witness dials of the experiment: `p ↦ (D | p)`, realized as a genuinely
periodic function by evaluating the Jacobi symbol at the reduced representative
modulo `4|D|`.  On odd candidates it agrees with `(D | ·)` on the nose. -/

/-- The Kronecker dial at a nonzero discriminant `D`, with conductor `4|D|`. -/
def kron (D : ℤ) (hD : D ≠ 0) : Dial where
  cond := 4 * D.natAbs
  cond_pos := by
    have : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
    omega
  chi := fun n => jacobiSym D (n % (4 * D.natAbs))
  periodic := fun n => by simp [Nat.add_mod_right]



/-! ## 2. Dial systems and the conductor lcm `M*` -/

variable {K : ℕ}

/-- The **dial vector** of a candidate: all `K` readings at once. -/
def dialVec (Ds : Fin K → Dial) (p : ℕ) : Fin K → ℤ := fun i => (Ds i).chi p

/-- `M*`: the lcm of the conductors of the dial system. -/
def condLcm (Ds : Fin K → Dial) : ℕ := Finset.univ.lcm (fun i => (Ds i).cond)





/-! ## 3. Counting the residues visible inside a hint class -/


/-! ## 4. The master bound: the amplification budget is `M* / gcd(M*, m)` -/



/-! ## 5. Regime 1 (`M* ∣ m`): the dials are constant, hence useless -/





/-! ## 6. Hint-computability, and the dichotomy -/

/-- A statistic is **hint-computable** when it is a function of the hint `p % m`
alone — i.e. the attacker can evaluate it from the Coppersmith hint. -/
def HintComputable {β : Type*} (m : ℕ) (T : ℕ → β) : Prop :=
  ∃ g : ℕ → β, ∀ p, T p = g (p % m)








/-! ## 7. The information-theoretic side: `K = Ω(log C)` dials are needed -/



/-! ## 8. The two experimental regimes, on the experiment's own numbers -/

section Regime1

/-- The Regime-1 dial system of the experiment: Kronecker dials at
`D = -3, 21, 42`, of conductors `12, 84, 168`. -/
def dials808 : Fin 3 → Dial :=
  ![kron (-3) (by norm_num), kron 21 (by norm_num), kron 42 (by norm_num)]







end Regime1

section Regime2

/-- The Regime-2 dial of the experiment: the Kronecker dial `(-4 | ·)`, of
conductor `16`.  The hint modulus is `m = 135`, and `16 ∤ 135`. -/
def dials340 : Fin 1 → Dial := ![kron (-4) (by norm_num)]







end Regime2

/-! ## 9. The verdict

`no_amplification_dichotomy` packages the closure: for every dial system and
every hint modulus, either the dials are hint-computable — and then they are
provably worthless on the candidate set, for every secret and every
post-processing — or they are not computable from the hint at all. -/


end DialThreshold


