-- Prove2me | solution 1 for Ma1Effectivity.signblind_misses_alignment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:05:54.150075+00:00
-- url     : https://prove2.me/submissions/febb7a9b-f8bb-4fc8-9ea7-ba25d8033a31

-- Sol generated from Bridges/Ma1EffectivitySignBlind.lean
import Mathlib
import Definitions.Def_Bridges_Ma1EffectivitySignBlind
import Theorems.Thm_Ma1Effectivity_align_tilted_eq
import Theorems.Thm_Ma1Effectivity_chiR_comp_neg

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

theorem maxDev_comp_perm [Nonempty ι] (c : ι → ℝ) (E : ℝ) (σ : Equiv.Perm ι) :
    maxDev (c ∘ σ) E = maxDev c E := by
  have key : (univ.sup' univ_nonempty fun a => |c (σ a) - E|)
      = univ.sup' univ_nonempty fun a => |c a - E| := by
    refine le_antisymm (Finset.sup'_le _ _ fun a _ => ?_) (Finset.sup'_le _ _ fun a _ => ?_)
    · exact Finset.le_sup' (fun a => |c a - E|) (mem_univ (σ a))
    · have := Finset.le_sup' (fun b => |c (σ b) - E|) (mem_univ (σ.symm a))
      simpa using this
  simpa [maxDev, Function.comp] using congrArg (fun t => t / Real.sqrt E) key

theorem chiSq_comp_perm (c : ι → ℝ) (E : ℝ) (σ : Equiv.Perm ι) :
    chiSq (c ∘ σ) E = chiSq c E := by
  have : ∑ a, (c (σ a) - E) ^ 2 = ∑ a, (c a - E) ^ 2 :=
    Fintype.sum_equiv σ _ _ (fun _ => rfl)
  simp [chiSq, Function.comp, this]

/-! ## Vacuity of the within-modulus permutation control -/




/-! ## Sign-blindness is a strict loss of information -/

/-- Reflecting a count field along an involution under which the weight is odd flips the
sign of the alignment. -/
theorem align_comp_of_odd (ν : Equiv.Perm ι) (w : ι → ℝ) (hw : ∀ a, w (ν a) = -w a)
    (c : ι → ℝ) : align (c ∘ ν) w = -align c w := by
  have h1 : ∑ a, c (ν a) * w a = ∑ a, -(c (ν a) * w (ν a)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hw a]; ring
  have h2 : ∑ a, c (ν a) * w (ν a) = ∑ a, c a * w a :=
    Fintype.sum_equiv ν _ _ (fun _ => rfl)
  simp only [align, Function.comp]
  rw [h1, Finset.sum_neg_distrib, h2]


/-! ## The arithmetic instance: quadratic characters mod `p ≡ 3 (mod 4)` -/

variable (p : ℕ) [Fact p.Prime]










open Ma1Effectivity in
theorem solution(hp3 : p % 4 = 3) (E : ℝ) :
    ∃ c₁ c₂ : ZMod p → ℝ,
      maxDev c₁ E = maxDev c₂ E ∧ chiSq c₁ E = chiSq c₂ E ∧
      align c₁ (chiR p) = ((p : ℝ) - 1) ∧ align c₂ (chiR p) = -((p : ℝ) - 1) ∧
      align c₁ (chiR p) ≠ align c₂ (chiR p) := by
  have hp : p ≠ 2 := by omega
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by
    have : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h | h
      · interval_cases p <;> omega
      · exact h
    exact_mod_cast this
  have hodd : ∀ a : ZMod p, chiR p (negPerm p a) = -chiR p a := by
    intro a; simpa [negPerm] using chiR_comp_neg p hp3 a
  set c : ZMod p → ℝ := fun a => E + chiR p a with hc
  have hval : align c (chiR p) = (p : ℝ) - 1 := align_tilted_eq p hp E
  have hrefl : align (c ∘ negPerm p) (chiR p) = -((p : ℝ) - 1) := by
    rw [align_comp_of_odd (negPerm p) (chiR p) hodd c, hval]
  refine ⟨c, c ∘ negPerm p, (maxDev_comp_perm c E (negPerm p)).symm,
    (chiSq_comp_perm c E (negPerm p)).symm, hval, hrefl, ?_⟩
  rw [hval, hrefl]
  intro h
  linarith
