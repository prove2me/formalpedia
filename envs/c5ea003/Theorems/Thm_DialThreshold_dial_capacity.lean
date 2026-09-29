-- Prove2me | Theorems.Thm_DialThreshold_dial_capacity
-- name    : DialThreshold.dial_capacity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:12:56.987686+00:00
-- url     : https://prove2.me/theorems/9d3b486c-8db4-4310-9b1f-2e928571449e
-- title:
--   Dial capacity.
-- statement:
--   **Dial capacity.**  A system of `K` sign dials (readings in `{-1, 0, 1}`,
--   which is the case for Kronecker symbols) has at most `3^K` distinct dial
--   vectors; so on more than `3^K` candidates two are always confused.  Pinning a
--   candidate set of size `C` therefore needs `K ≥ log₃ C` dials — the `Θ(log N)`
--   threshold of the experiment.
--
--   ```lean
--   theorem DialThreshold.dial_capacity(Ds : Fin K → Dial) (Ω : Finset ℕ)
--       (hsign : ∀ (i : Fin K) (p : ℕ), (Ds i).chi p ∈ ({-1, 0, 1} : Finset ℤ))
--       (hcard : 3 ^ K < Ω.card) :
--       ∃ p ∈ Ω, ∃ q ∈ Ω, p ≠ q ∧ dialVec Ds p = dialVec Ds q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DialThresholdNoAmplification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DialThresholdNoAmplification.lean#L349

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



/-! ## 5. Regime 1 (`M* ∣ m`): the dials are constant, hence useless -/





/-! ## 6. Hint-computability, and the dichotomy -/









/-! ## 7. The information-theoretic side: `K = Ω(log C)` dials are needed -/

theorem DialThreshold.dial_capacity(Ds : Fin K → Dial) (Ω : Finset ℕ)
    (hsign : ∀ (i : Fin K) (p : ℕ), (Ds i).chi p ∈ ({-1, 0, 1} : Finset ℤ))
    (hcard : 3 ^ K < Ω.card) :
    ∃ p ∈ Ω, ∃ q ∈ Ω, p ≠ q ∧ dialVec Ds p = dialVec Ds q := by sorry
