-- Prove2me | Theorems.Thm_Ma1Effectivity_align_tilted_eq
-- name    : Ma1Effectivity.align_tilted_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:02.394186+00:00
-- url     : https://prove2.me/theorems/7d9951fe-0283-4e37-8d32-8afbaef4e7dc
-- title:
--   The character-tilted count field `E + χ` has maximal alignment `p − 1` with `χ`.
-- statement:
--   The character-tilted count field `E + χ` has maximal alignment `p − 1` with `χ`.
--
--   ```lean
--   theorem Ma1Effectivity.align_tilted_eq(hp : p ≠ 2) (E : ℝ) :
--       align (fun a => E + chiR p a) (chiR p) = (p : ℝ) - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/Ma1EffectivitySignBlind.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/Ma1EffectivitySignBlind.lean#L174

-- Thm stub generated from Bridges/Ma1EffectivitySignBlind.lean
import Mathlib
import Definitions.Def_Bridges_Ma1EffectivitySignBlind

/-!
# Sign-blind deviation readouts: what the MA-1 effectivity sweep can and cannot see

Experiment 566 (paper 213) regresses the arithmetic-progression deviation readout

  `D(m) = max_a |π(x;m,a) − E| / √E`,   secondary `χ²(m) = Σ_a (π(x;m,a) − E)²/E`

on the quadratic-character L-mass `P(m) = Σ_χ |L(1,χ)|`, and records a pre-registered
null (`R² = 0.0187` at `x = 2^26`, `R² = 0.0785` at `x = 2^28`, both far below the
`0.5` bar).  Two methodological items in the ledger are *mathematical* statements, not
statistics, and this file proves them.

1. **The within-modulus permutation control is vacuous.**  Both registered readouts are
   symmetric functions of the residue-class counts.  Consequently the permutation
   p-value of either readout is *exactly* `1` for every count field, whatever the
   arithmetic: the control can never reject.  (`maxDev_comp_perm`, `chiSq_comp_perm`,
   `permPValue_eq_one_of_invariant`, `permutation_control_vacuous`.)

2. **The readout is sign-blind, and sign-blindness is a genuine loss.**  The signed
   character alignment `align c χ = Σ_a c a · χ(a)` is *not* a function of the
   permutation-invariant readouts.  For every prime `p ≡ 3 (mod 4)` we exhibit two
   count fields on `ZMod p` — one the negation-reflection of the other — with *identical*
   `maxDev` and `χ²` but with alignments of opposite sign and of maximal size `p − 1`.
   (`align_comp_of_odd`, `quadraticChar_comp_neg`, `signblind_misses_alignment`.)

Item 2 is the formal content of the paper's prominent scoping caveat: the recorded null
bounds the *magnitude* route only; a signed character-alignment analysis is a strictly
finer instrument, and cannot be inferred from the recorded statistics.

Nothing here is asymptotic or model-dependent: all statements are exact identities about
finite count fields.
-/

open Ma1Effectivity

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## The two registered readouts, and the signed alignment -/




/-! ## Both readouts are permutation invariant -/



/-! ## Vacuity of the within-modulus permutation control -/




/-! ## Sign-blindness is a strict loss of information -/



/-! ## The arithmetic instance: quadratic characters mod `p ≡ 3 (mod 4)` -/

variable (p : ℕ) [Fact p.Prime]

theorem Ma1Effectivity.align_tilted_eq(hp : p ≠ 2) (E : ℝ) :
    align (fun a => E + chiR p a) (chiR p) = (p : ℝ) - 1 := by sorry
