-- Prove2me | solution 1 for EOSGenericity.probIndep_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T23:37:22.945294+00:00
-- url     : https://prove2.me/submissions/795b68a3-fea2-40fa-b5a4-14d5d6e097a8

-- Sol generated from NumberTheory/EOSExclusiveDimGenericity.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
import Theorems.Thm_EOSWidthRamp_card_eq_pow_finrank_zmod
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
theorem solution{k : ℕ} (hk : k ≤ finrank (ZMod p) V) :
    probIndep p V k
      = ∏ i ∈ range k, (1 - (p : ℝ) ^ i / (p : ℝ) ^ (finrank (ZMod p) V)) := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set n := finrank (ZMod p) V with hn
  have hcardV : Nat.card V = p ^ n := EOSWidthRamp.card_eq_pow_finrank_zmod (p := p) V
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  have hcount : Nat.card {s : Fin k → V // LinearIndependent (ZMod p) s}
      = ∏ i : Fin k, (p ^ n - p ^ (i : ℕ)) := by
    have := card_linearIndependent (K := ZMod p) (V := V) (k := k) (by simpa [hn] using hk)
    simpa [hq, hn] using this
  have hcast : ((∏ i : Fin k, (p ^ n - p ^ (i : ℕ)) : ℕ) : ℝ)
      = ∏ i ∈ range k, ((p : ℝ) ^ n - (p : ℝ) ^ i) := by
    rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((p ^ n - p ^ i : ℕ) : ℝ))]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hle : p ^ i ≤ p ^ n :=
      Nat.pow_le_pow_right (le_of_lt hp) (le_trans (le_of_lt (mem_range.mp hi)) hk)
    push_cast [Nat.cast_sub hle]
    ring
  have hpow : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  rw [probIndep, hcount, hcast, hcardV]
  push_cast
  rw [← pow_mul]
  have : ∏ i ∈ range k, ((p : ℝ) ^ n - (p : ℝ) ^ i)
      = (∏ i ∈ range k, (1 - (p : ℝ) ^ i / (p : ℝ) ^ n)) * ((p : ℝ) ^ n) ^ k := by
    have hfac : ∀ i ∈ range k, ((p : ℝ) ^ n - (p : ℝ) ^ i)
        = (1 - (p : ℝ) ^ i / (p : ℝ) ^ n) * (p : ℝ) ^ n := by
      intro i _
      field_simp
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, card_range]
  rw [this, pow_mul]
  field_simp
