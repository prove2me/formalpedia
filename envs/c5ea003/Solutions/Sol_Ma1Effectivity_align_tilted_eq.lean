-- Prove2me | solution 1 for Ma1Effectivity.align_tilted_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:03:02.422285+00:00
-- url     : https://prove2.me/submissions/032d97ac-fdfb-4bfa-a29f-ea958be8057c

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


theorem chiR_sq_one {a : ZMod p} (ha : a ≠ 0) : chiR p a ^ 2 = 1 := by
  have h : (quadraticChar (ZMod p) a) ^ 2 = 1 := quadraticChar_sq_one ha
  have : ((quadraticChar (ZMod p) a : ℤ) : ℝ) ^ 2 = ((1 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [chiR] using this

theorem chiR_zero : chiR p 0 = 0 := by simp [chiR]

theorem chiR_sum_zero (hp : p ≠ 2) : ∑ a : ZMod p, chiR p a = 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact_mod_cast hp
  have h := quadraticChar_sum_zero (F := ZMod p) hchar
  have : ((∑ a : ZMod p, quadraticChar (ZMod p) a : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [chiR, Int.cast_sum] using this






open Ma1Effectivity in
theorem solution(hp : p ≠ 2) (E : ℝ) :
    align (fun a => E + chiR p a) (chiR p) = (p : ℝ) - 1 := by
  have hsplit : align (fun a => E + chiR p a) (chiR p)
      = E * (∑ a : ZMod p, chiR p a) + ∑ a : ZMod p, chiR p a ^ 2 := by
    simp only [align]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, chiR_sum_zero p hp, mul_zero, zero_add]
  have hzero : (0 : ZMod p) ∈ (univ : Finset (ZMod p)) := mem_univ 0
  have hone : ∀ a ∈ (univ : Finset (ZMod p)).erase 0, chiR p a ^ 2 = 1 :=
    fun a ha => chiR_sq_one p (Finset.ne_of_mem_erase ha)
  have hcard : (univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (Nat.Prime.pos (Fact.out (p := p.Prime))).ne'
  rw [← Finset.sum_erase_add univ _ hzero, Finset.sum_congr rfl hone, Finset.sum_const,
    Finset.card_erase_of_mem hzero, hcard, chiR_zero, nsmul_eq_mul, mul_one, Nat.cast_sub hp1]
  norm_num
