-- Prove2me | solution 1 for DiophantineLattice.halfPt_multiplicity_even
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:43:01.937991+00:00
-- url     : https://prove2.me/submissions/935bea92-bd0e-4ae4-b68e-e4d522755442

-- Sol generated from Novelty/DiophantineLatticeTorsionGap.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
import Theorems.Thm_DiophantineLattice_emb_ne_zero
import Theorems.Thm_DiophantineLattice_halfPt_antipode_form
import Theorems.Thm_DiophantineLattice_sub_two_smul_ne_zero

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
theorem solution{B : Matrix (Fin n) (Fin n) ℚ} (hpd : PosDef B) {lam : ℚ}
    (h : IsMinEnergy B lam) {v : Fin n → ℤ} (hv : form B (emb v) = lam) (c : ℚ)
    (S : Finset (Fin n → ℤ))
    (hS : ∀ m : Fin n → ℤ, m ∈ S ↔ form B (fun i => halfPt v i - emb m i) = c) :
    Even S.card := by
  classical
  obtain ⟨⟨w, hw, hwlam⟩, hmin⟩ := h
  have hpos : 0 < lam := by rw [← hwlam]; exact hpd _ (emb_ne_zero hw)
  set g : (Fin n → ℤ) → (Fin n → ℤ) := fun m => fun j => v j - m j with hg
  have hgmem : ∀ m ∈ S, g m ∈ S := by
    intro m hm
    rw [hS] at hm ⊢
    rw [halfPt_antipode_form]
    exact hm
  have hginv : ∀ m, g (g m) = m := by
    intro m; funext j; simp [hg]
  have hgfix : ∀ m ∈ S, g m ≠ m := by
    intro m _ hfix
    have hvm : ∀ i, v i - 2 * m i = 0 := by
      intro i
      have : (g m) i = m i := by rw [hfix]
      simp only [hg] at this
      omega
    exact sub_two_smul_ne_zero hpos hmin hv m (funext hvm)
  have hsum : ∑ _x ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => g a) (fun a _ => by decide)
      (fun a ha _ => hgfix a ha) (fun a ha => hgmem a ha) (fun a _ => hginv a)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum
