-- Prove2me | Theorems.Thm_DialThreshold_card_image_dialVec_le
-- name    : DialThreshold.card_image_dialVec_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:11:05.613172+00:00
-- url     : https://prove2.me/theorems/0750da25-22b0-47a7-bc18-5379a18a53f2
-- title:
--   Master bound.
-- statement:
--   **Master bound.**  On a candidate set contained in a single hint class
--   `p ≡ r (mod m)`, the dial vector takes at most `M* / gcd(M*, m)` distinct
--   values.  Everything else in this file is a consequence of this one inequality:
--   the *entire* discriminating power of the dials, beyond the hint, is the index
--   `M*/gcd(M*, m)` by which the dial resolution overshoots the hint.
--
--   ```lean
--   theorem DialThreshold.card_image_dialVec_le(Ds : Fin K → Dial) (Ω : Finset ℕ) {m r : ℕ} (hm : 0 < m)
--       (hΩ : ∀ p ∈ Ω, p % m = r % m) :
--       (Ω.image (dialVec Ds)).card ≤ condLcm Ds / Nat.gcd (condLcm Ds) m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DialThresholdNoAmplification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DialThresholdNoAmplification.lean#L180

-- Thm stub generated from Combinatorics/DialThresholdNoAmplification.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
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

open DialThreshold

open Finset

/-! ## 1. Residue dials -/


open Dial

variable (d : Dial)





/-! ### Kronecker dials

The free-witness dials of the experiment: `p ↦ (D | p)`, realized as a genuinely
periodic function by evaluating the Jacobi symbol at the reduced representative
modulo `4|D|`.  On odd candidates it agrees with `(D | ·)` on the nose. -/




/-! ## 2. Dial systems and the conductor lcm `M*` -/

variable {K : ℕ}







/-! ## 3. Counting the residues visible inside a hint class -/


/-! ## 4. The master bound: the amplification budget is `M* / gcd(M*, m)` -/

theorem DialThreshold.card_image_dialVec_le(Ds : Fin K → Dial) (Ω : Finset ℕ) {m r : ℕ} (hm : 0 < m)
    (hΩ : ∀ p ∈ Ω, p % m = r % m) :
    (Ω.image (dialVec Ds)).card ≤ condLcm Ds / Nat.gcd (condLcm Ds) m := by sorry
