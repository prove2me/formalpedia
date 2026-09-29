-- Prove2me | solution 1 for EOSGenericity.prob_indep_and_cure_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T23:52:14.385172+00:00
-- url     : https://prove2.me/submissions/e8001879-0137-4ee3-9e55-e91cd7e9005e

-- Sol generated from NumberTheory/EOSExclusiveDimGenericity.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
import Theorems.Thm_EOSGenericity_probIndep_ge
import Theorems.Thm_EOSWidthRamp_card_V_pos
import Theorems.Thm_EOSWidthRamp_failProb_le
/-
# Are the exclusive dimensions really exclusive?  A `q`-Pochhammer genericity bound

Companion to `Catalog/NumberTheory/EOSWidthMonotoneRamp.lean`.

The ramp model draws the boundary token's `k` exclusive directions uniformly at random from a
finite `𝔽_p`-space `V` of dimension `n`.  For the phrase "`k` exclusive dimensions" to be
honest, the `k` draws must actually be linearly independent.  This file quantifies that:

* `EOSGenericity.probIndep_eq_prod` — the probability that `k ≤ n` uniform draws are linearly
  independent is exactly the `q`-Pochhammer product `∏_{i<k} (1 - p^{i-n})`
  (via Mathlib's `card_linearIndependent`);
* `EOSGenericity.one_sub_sum_le_prod_one_sub` — a Weierstrass product inequality, proved by
  induction;
* `EOSGenericity.probIndep_ge` — hence `P(independent) ≥ 1 - (p^k - 1)/((p-1) p^n)`: for
  `k ≪ n` the drawn directions are exclusive with overwhelming probability, so the model of
  the companion file is not vacuous;
* `EOSGenericity.probIndep_antitone_step` — genericity decays with `k`, in the opposite
  direction to the reliability ramp;
* `EOSGenericity.prob_indep_and_cure_ge` — **the synthesis**: with `k` exclusive dimensions the
  probability that the token both occupies a genuine `k`-dimensional subspace *and* escapes all
  `m` obstructions is at least

  `1 - m·p^{-k} - (p^k - 1)/((p-1)·p^n)`,

  a two-sided window: the first term (reliability) shrinks geometrically in `k`, the second
  (genericity) grows geometrically in `k`, so the optimal exclusive width is interior — there is
  a genuine trade-off and no cliff.

### Lab notes

With `p = 2`, `n = 192` (the hidden width of the recurrent cell in the motivating experiment)
and `m = 1`, the bound reads `1 - 2^{-k} - (2^k-1)·2^{-192}`: the genericity loss is utterly
negligible up to `k ≈ 100`, so in the regime of the data (`k ≤ 8`) the reliability term alone
governs, matching the observed monotone ramp `0.25 → 0.33 → 0.83 → 1.00 → 1.00`.
-/


open Module Finset

open EOSGenericity

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]






/-! ## Synthesis: reliability and genericity together -/



open EOSGenericity in
open EOSWidthRamp in
theorem solution(W : Fin m → Submodule (ZMod p) V) (hW : ∀ j, W j ≠ ⊤) {k : ℕ}
    (hk : k ≤ finrank (ZMod p) V) :
    1 - (m : ℝ) / (p : ℝ) ^ k
        - ((p : ℝ) ^ k - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ (finrank (ZMod p) V))
      ≤ (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
          / (Nat.card V : ℝ) ^ k := by
  classical
  have hNpos : (0 : ℝ) < (Nat.card V : ℝ) ^ k :=
    pow_pos (by exact_mod_cast (EOSWidthRamp.card_V_pos (V := V))) k
  -- set-level union bound: independent ⊆ (independent ∧ cured) ∪ failing
  set I : Set (Fin k → V) := {v | LinearIndependent (ZMod p) v} with hI
  set G : Set (Fin k → V) := {v | LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} with hG
  set F : Set (Fin k → V) := {v | ∃ j, ∀ i, v i ∈ W j} with hF
  have hsub : I ⊆ G ∪ F := by
    intro v hv
    by_cases hfail : ∃ j, ∀ i, v i ∈ W j
    · exact Or.inr hfail
    · exact Or.inl ⟨hv, hfail⟩
  have hcard : Nat.card I ≤ Nat.card G + Nat.card F := by
    have h1 : I.ncard ≤ (G ∪ F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (G ∪ F).ncard ≤ G.ncard + F.ncard := Set.ncard_union_le G F
    simpa [Nat.card_coe_set_eq] using le_trans h1 h2
  have hIcard : (Nat.card I : ℝ)
      = (Nat.card {s : Fin k → V // LinearIndependent (ZMod p) s} : ℝ) := rfl
  have hFcard : (Nat.card F : ℝ) = (EOSWidthRamp.failCount W k : ℝ) := rfl
  have hGcard : (Nat.card G : ℝ)
      = (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ) :=
    rfl
  have hcardR : (Nat.card {s : Fin k → V // LinearIndependent (ZMod p) s} : ℝ)
      ≤ (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
        + (EOSWidthRamp.failCount W k : ℝ) := by
    rw [← hIcard, ← hGcard, ← hFcard]
    exact_mod_cast hcard
  have hdiv := (div_le_div_iff_of_pos_right hNpos).mpr hcardR
  have hgen := probIndep_ge (p := p) (V := V) hk
  have hfail := EOSWidthRamp.failProb_le W hW k
  rw [probIndep] at hgen
  rw [EOSWidthRamp.failProb] at hfail
  have hsplit : ((Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
      + (EOSWidthRamp.failCount W k : ℝ)) / (Nat.card V : ℝ) ^ k
      = (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
          / (Nat.card V : ℝ) ^ k
        + (EOSWidthRamp.failCount W k : ℝ) / (Nat.card V : ℝ) ^ k := by
    rw [add_div]
  have hle : (Nat.card {s : Fin k → V // LinearIndependent (ZMod p) s} : ℝ)
        / (Nat.card V : ℝ) ^ k
      ≤ (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
          / (Nat.card V : ℝ) ^ k
        + (EOSWidthRamp.failCount W k : ℝ) / (Nat.card V : ℝ) ^ k := by
    rw [← hsplit]; exact hdiv
  linarith
