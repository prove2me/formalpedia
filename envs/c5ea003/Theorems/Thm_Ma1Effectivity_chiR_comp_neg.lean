-- Prove2me | Theorems.Thm_Ma1Effectivity_chiR_comp_neg
-- name    : Ma1Effectivity.chiR_comp_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:36.070564+00:00
-- url     : https://prove2.me/theorems/39cfde99-ef4e-4882-aad1-12e39b146f6d
-- title:
--   For `p ≡ 3 (mod 4)` the quadratic character is odd: `χ(−a) = −χ(a)`.
-- statement:
--   For `p ≡ 3 (mod 4)` the quadratic character is **odd**: `χ(−a) = −χ(a)`.
--
--   ```lean
--   theorem Ma1Effectivity.chiR_comp_neg(hp3 : p % 4 = 3) (a : ZMod p) : chiR p (-a) = -chiR p a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/Ma1EffectivitySignBlind.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/Ma1EffectivitySignBlind.lean#L154

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

theorem Ma1Effectivity.chiR_comp_neg(hp3 : p % 4 = 3) (a : ZMod p) : chiR p (-a) = -chiR p a := by sorry
