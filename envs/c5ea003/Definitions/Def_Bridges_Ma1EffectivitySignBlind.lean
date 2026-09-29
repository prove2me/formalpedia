-- Prove2me | Definitions.Def_Bridges_Ma1EffectivitySignBlind
-- name    : Bridges_Ma1EffectivitySignBlind
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:52.842867+00:00
-- url     : https://prove2.me/theorems/7d68d296-2cb6-47f2-a47d-9ea28a006cb2
-- title:
--   Aether Catalog definitions — Bridges_Ma1EffectivitySignBlind
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.Ma1EffectivitySignBlind`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/Ma1EffectivitySignBlind.lean by skeleton subtraction
import Mathlib

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

namespace Ma1Effectivity

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## The two registered readouts, and the signed alignment -/

/-- The registered primary readout: the normalised maximal deviation of a count field `c`
from its expectation `E` over the residue classes. -/
noncomputable def maxDev [Nonempty ι] (c : ι → ℝ) (E : ℝ) : ℝ :=
  (univ.sup' univ_nonempty fun a => |c a - E|) / Real.sqrt E

/-- The registered secondary readout: the `χ²` statistic of a count field. -/
noncomputable def chiSq (c : ι → ℝ) (E : ℝ) : ℝ := (∑ a, (c a - E) ^ 2) / E

/-- The *signed* character alignment of a count field with a weight `w` (in practice a real
Dirichlet character).  This is the functional that the sign-blind readouts discard. -/
def align (c w : ι → ℝ) : ℝ := ∑ a, c a * w a

/-! ## Both readouts are permutation invariant -/



/-! ## Vacuity of the within-modulus permutation control -/

open scoped Classical in
/-- The one-sided permutation p-value of a statistic `T` on a count field `c`: the fraction
of relabelings of the residue classes whose statistic is at least the observed one. -/
noncomputable def permPValue (T : (ι → ℝ) → ℝ) (c : ι → ℝ) : ℝ :=
  ((univ.filter fun σ : Equiv.Perm ι => T c ≤ T (c ∘ σ)).card : ℝ) /
    (Fintype.card (Equiv.Perm ι) : ℝ)



/-! ## Sign-blindness is a strict loss of information -/



/-! ## The arithmetic instance: quadratic characters mod `p ≡ 3 (mod 4)` -/

variable (p : ℕ) [Fact p.Prime]

/-- The real-valued quadratic character mod `p`. -/
noncomputable def chiR (a : ZMod p) : ℝ := ((quadraticChar (ZMod p) a : ℤ) : ℝ)





/-- The reflection `a ↦ −a` of the residue classes. -/
def negPerm : Equiv.Perm (ZMod p) := Equiv.neg (ZMod p)



end Ma1Effectivity


