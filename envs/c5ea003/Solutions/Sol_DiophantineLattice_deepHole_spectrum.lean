-- Prove2me | solution 1 for DiophantineLattice.deepHole_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:21:14.371394+00:00
-- url     : https://prove2.me/submissions/3ab7242f-023b-4bb6-b005-99d66471c856

-- Sol generated from Novelty/DiophantineLatticeShiftedTheta.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Theorems.Thm_DiophantineLattice_form_one

/-!
# The shifted theta spectrum of `ℤⁿ` at its deep hole

Continuing `Novelty/DiophantineLatticeSpectralGap.lean`, we analyse the non-homogeneous form
`F(x) = Q(x - t)` for the standard form `Q(x) = Σ xᵢ²` on `ℤⁿ` and the **deep hole**
`t = (1/2, …, 1/2)`.  Two independent phenomena are isolated.

* *Metric*: the spectral gap at the deep hole is exactly `n/4` (`deepHole_isInhomMin`), and
  `n/4` is also an upper bound for the inhomogeneous minimum at **every** shift
  (`standard_covering_le`).  Hence the covering radius² of `ℤⁿ` is exactly `n/4`
  (`standard_covering_radius_least`).  Compared with `covering_ge_quarter_min` (which only
  gives `≥ 1/4`), this shows the packing–covering inequality is very far from an equality in
  large dimension (`covering_exceeds_quarter_min`).
* *Arithmetic*: the whole value set (the support of the shifted theta series) is contained in
  `n/4 + 2ℤ≥0` (`deepHole_spectrum`), because a sum of `n` odd squares is `≡ n (mod 8)`.  So
  consecutive attained values differ by at least `2` (`deepHole_gap_two`), and this is
  attained (`deepHole_gap_two_attained`).  In particular the non-homogeneous equation
  `Σ (2xᵢ - 1)² = N` is unsolvable unless `N ≡ n (mod 8)`, `N ≥ n`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the deep-hole shifted theta series of `ℤⁿ` should have a *doubled*
gap, i.e. its support sits in an arithmetic progression of step `2` rather than `1`.
Experiment (Experimenter): exhaustive rational enumeration of `4·Q(t-m)` over `m ∈ {-2..2}ⁿ`
for `n ≤ 4` produced exactly the residues `{n, n+8, n+16, …}` (see `ComputationalEvidence.md`);
no value `≡ n+4 (mod 8)` ever appeared, ruling out step `1`.
Analysis (Analyst): the mechanism is `(1-2m)² = 8·m(m-1)/2 + 1` with `m(m-1)/2 ≥ 0` an
integer — a `2`-adic statement, entirely independent of the metric statement `μ = n/4`, which
is a rounding/convexity statement.  The two combine into: the smallest attained value is `n/4`
and the next possible one is `n/4 + 2`.
Critique (Critic): `deepHole_gap_two` is not vacuous — both `n/4` and `n/4 + 2` are attained
(`deepHole_mem_spectrum`, `deepHole_gap_two_attained`) for `n ≥ 1`; and it is genuinely
stronger than integrality, which would only give step `1/4` here.
Synthesis (PI): the deep hole of `ℤⁿ` carries a spectral gap of size `2` in the value spectrum
*and* an inhomogeneous minimum of `n/4` — two different senses of "gap" for the same
non-homogeneous form, one archimedean, one `2`-adic.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}


/-! ## Metric part: the inhomogeneous minimum at the deep hole is `n/4` -/








/-! ## Arithmetic part: the `2`-adic gap in the shifted spectrum -/

/-- Every odd square is `1` modulo `8`, with a *nonnegative* quotient. -/
lemma odd_sq_eq_one_add_eight (m : ℤ) : ∃ k : ℤ, 0 ≤ k ∧ (1 - 2 * m) ^ 2 = 1 + 8 * k := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m * (m - 1) = 2 * j := by
    rcases Int.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (m - 1), by rw [ht]; ring⟩
    · exact ⟨m * t, by rw [ht]; ring⟩
  refine ⟨j, ?_, by linarith [hj, sq_nonneg (1 - 2 * m)] ⟩
  · have hnn : 0 ≤ m * (m - 1) := by
      rcases (by omega : m ≤ 0 ∨ 1 ≤ m) with h | h <;> nlinarith
    omega

/-- The integral avatar of the shifted form: `4·Q(t - m) = Σ (1 - 2mᵢ)²`. -/
lemma four_mul_deepHole_form (m : Fin n → ℤ) :
    4 * form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
      = ((∑ i, (1 - 2 * m i) ^ 2 : ℤ) : ℚ) := by
  rw [form_one, mul_sum]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  simp only [deepHole, emb]
  ring






open DiophantineLattice in
theorem solution(m : Fin n → ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧
      form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
        = (n : ℚ) / 4 + 2 * k := by
  choose k hk0 hk using fun i : Fin n => odd_sq_eq_one_add_eight (m i)
  refine ⟨∑ i, k i, sum_nonneg fun i _ => hk0 i, ?_⟩
  have hsum : (∑ i, (1 - 2 * m i) ^ 2 : ℤ) = n + 8 * ∑ i, k i := by
    rw [sum_congr rfl fun i _ => hk i, sum_add_distrib, ← mul_sum]
    simp [sum_const, card_univ]
  have h4 := four_mul_deepHole_form m
  rw [hsum] at h4
  push_cast at h4 ⊢
  linarith
