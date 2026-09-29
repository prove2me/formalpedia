-- Prove2me | solution 1 for Ma1Effectivity.chiR_comp_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:03:02.876392+00:00
-- url     : https://prove2.me/submissions/16574151-9240-4ed7-85bd-464b35a27609

-- Sol generated from Bridges/Ma1EffectivitySignBlind.lean
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










open Ma1Effectivity in
theorem solution(hp3 : p % 4 = 3) (a : ZMod p) : chiR p (-a) = -chiR p a := by
  have hp : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, hcard]
    exact ZMod.χ₄_nat_three_mod_four hp3
  have hmul : quadraticChar (ZMod p) (-a)
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) a := by
    rw [← map_mul]; ring_nf
  have : ((quadraticChar (ZMod p) (-a) : ℤ) : ℝ)
      = -((quadraticChar (ZMod p) a : ℤ) : ℝ) := by
    rw [hmul, hneg]; push_cast; ring
  simpa [chiR] using this
