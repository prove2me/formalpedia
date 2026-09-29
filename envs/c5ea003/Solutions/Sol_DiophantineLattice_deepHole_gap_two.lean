-- Prove2me | solution 1 for DiophantineLattice.deepHole_gap_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:29:09.227451+00:00
-- url     : https://prove2.me/submissions/95f581ac-9c8c-4a3c-ae89-fe6093aa864c

-- Sol generated from Novelty/DiophantineLatticeShiftedTheta.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Theorems.Thm_DiophantineLattice_deepHole_spectrum

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
theorem solution(m m' : Fin n → ℤ)
    (hne : form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
      ≠ form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m' i)) :
    2 ≤ |form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
      - form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m' i)| := by
  obtain ⟨k, _, hk⟩ := deepHole_spectrum m
  obtain ⟨k', _, hk'⟩ := deepHole_spectrum m'
  have hkk : k ≠ k' := by
    rintro rfl
    exact hne (by rw [hk, hk'])
  have hdiff : form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
      - form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m' i)
      = 2 * ((k : ℚ) - k') := by rw [hk, hk']; ring
  rw [hdiff, abs_mul]
  have h0 : (1 : ℤ) ≤ |k - k'| := Int.one_le_abs (sub_ne_zero.mpr hkk)
  have h1 : (1 : ℚ) ≤ |(k : ℚ) - k'| := by exact_mod_cast h0
  have habs : |(2 : ℚ)| = 2 := by norm_num
  rw [habs]
  linarith
