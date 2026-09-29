-- Prove2me | solution 1 for DiophantineLattice.standard_covering_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:47:27.648188+00:00
-- url     : https://prove2.me/submissions/acbe90df-4525-42a8-a231-5c6c6c2f8fb5

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








open DiophantineLattice in
theorem solution(t : Fin n → ℚ) :
    ∃ m : Fin n → ℤ, form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => t i - emb m i)
      ≤ (n : ℚ) / 4 := by
  refine ⟨fun i => round (t i), ?_⟩
  rw [form_one]
  have hterm : ∀ i : Fin n, (t i - emb (fun i => round (t i)) i) ^ 2 ≤ (1 : ℚ) / 4 := by
    intro i
    have h := abs_sub_round (t i)
    have h2 : |t i - (round (t i) : ℚ)| ^ 2 ≤ ((1 : ℚ) / 2) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) h
    simpa [sq_abs, emb] using h2.trans_eq (by norm_num)
  have h := sum_le_card_nsmul (univ : Finset (Fin n))
    (fun i => (t i - emb (fun i => round (t i)) i) ^ 2) ((1 : ℚ) / 4) (fun i _ => hterm i)
  simpa [nsmul_eq_mul, div_eq_mul_inv] using h
