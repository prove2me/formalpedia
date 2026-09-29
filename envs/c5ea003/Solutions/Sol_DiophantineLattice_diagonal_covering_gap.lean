-- Prove2me | solution 1 for DiophantineLattice.diagonal_covering_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:29:11.099199+00:00
-- url     : https://prove2.me/submissions/73dca24b-a613-4d6b-bceb-f3a38ab93b46

-- Sol generated from Novelty/DiophantineLatticeTorsionGap.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap

/-!
# Torsion refinement: spectral gaps at `r`-torsion points, and even multiplicities

Cycle 2 of the research thread.  `Novelty/DiophantineLatticeSpectralGap.lean` proved that the
non-homogeneous form `x ↦ Q(x - v/2)` attached to a shortest lattice vector `v` has spectral
gap exactly `λ₁/4`.  Here the `2` is replaced by an arbitrary `r ≥ 2`, i.e. the shift is an
arbitrary `r`-torsion point of `(L ⊗ ℚ)/L` of the special shape `v/r`:

* `torsion_gap_ge` : if `v ∉ rL` then `Q(v/r - m) ≥ λ₁/r²` for every lattice point `m`;
* `frac_shortest_isInhomMin` : for a shortest `v` and `r ≥ 2` the spectral gap at `v/r` is
  *exactly* `λ₁/r²` — the `r = 2` case is the previous cycle's main theorem;
* `torsion_no_integral_solution` : the Diophantine corollary, `Q(x - v/r) = c` is unsolvable
  in integers for `c < λ₁/r²`.

A second, independent structural theorem concerns *multiplicities* rather than sizes: the
antipodal involution `m ↦ v - m` acts freely on the solution set of `Q(x - v/2) = c`, hence

* `halfPt_multiplicity_even` : every coefficient of the theta series of the non-homogeneous
  form at a half shortest vector is **even**.

Finally the diagonal case is worked out completely: `diagonal_isMinEnergy` computes `λ₁` and
`diagonal_covering_radius_least` / `diagonal_covering_le` compute the covering radius² as
`(Σ aᵢ)/4`, so that the ratio covering/packing is `(Σ aᵢ)/(min aᵢ)`, unbounded.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the factor `1/4` of cycle 1 is the `r = 2` shadow of a general
`1/r²` law indexed by the torsion order of the shift; moreover multiplicities in the shifted
theta series should always be even.
Experiment (Experimenter): the halving identity `Q(v/r - m) = Q(v - rm)/r²` and the
obstruction `v ∈ rL ⇒ Q(v) = r²Q(v/r) ≥ r²λ₁ > λ₁` both survive verbatim for every `r ≥ 2`;
the involution `m ↦ v - m` is fixed-point free precisely because `v ∉ 2L`, which is the *same*
obstruction.  So one lemma (`sub_two_smul_ne_zero` and its `r`-analogue) drives both results.
Analysis (Analyst): the two cycle-1 phenomena are thus explained by a single structural fact —
a shortest vector is primitive modulo `r` for every `r ≥ 2`.  What genuinely fails to
generalise is the involution: for `r ≥ 3` the map `m ↦ v - m` is not a symmetry of the shifted
form, so "even multiplicity" is special to `2`-torsion (it becomes "divisible by the order of
the stabiliser-free symmetry group" in general — see FUTURE_DIRECTIONS).
Critique (Critic): `halfPt_multiplicity_even` is stated for an arbitrary `Finset` enumerating
the solutions, so it is not vacuous for `S = ∅` only; `frac_shortest_isInhomMin` includes the
attainment clause, so it is an identity, not a one-sided bound.
Synthesis (PI): spectral gap `λ₁/r²` at `r`-torsion shifts, even theta coefficients at
`2`-torsion shifts, and an exact covering radius `(Σaᵢ)/4` in the diagonal case.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## Gaps at `r`-torsion shifts -/







/-! ## Even multiplicities in the shifted theta series -/




/-! ## The diagonal case, computed completely -/








open DiophantineLattice in
theorem solution{a : Fin n → ℚ} (ha : ∀ i, 0 < a i) (i0 : Fin n)
    (hn : 2 ≤ n) : a i0 / 4 < (∑ i, a i) / 4 := by
  have hlt : a i0 < ∑ i, a i := by
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i0 := by
      have : 1 < Fintype.card (Fin n) := by simpa using hn
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card this i0
      exact ⟨j, hj⟩
    have hsub : a i0 + a j ≤ ∑ i, a i := by
      have := Finset.add_sum_erase (univ.erase i0) a (mem_erase.mpr ⟨hj, mem_univ j⟩)
      have h2 : a i0 + ∑ i ∈ univ.erase i0, a i = ∑ i, a i :=
        Finset.add_sum_erase univ a (mem_univ i0)
      have h3 : a j ≤ ∑ i ∈ univ.erase i0, a i :=
        single_le_sum (f := a) (fun k _ => (ha k).le) (mem_erase.mpr ⟨hj, mem_univ j⟩)
      linarith
    have := ha j
    linarith
  linarith
