-- Prove2me | solution 1 for DiophantineLattice.halfPt_multiplicity_even_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:43:02.440516+00:00
-- url     : https://prove2.me/submissions/137c893a-5547-4c1f-b781-d2d0f58ce273

-- Sol generated from Novelty/DiophantineLatticeMultiplicity.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Theorems.Thm_DiophantineLattice_halfPt_antipode_form

/-!
# Cycle 7: the parity criterion for shifted theta coefficients

Cycle 2 proved that all coefficients of the shifted theta series of `x ↦ Q(x - v/2)` are even
when `v` is a *shortest* vector (`halfPt_multiplicity_even`).  Conjecture 2 of
`FUTURE_DIRECTIONS.md` asserted that evenness is in fact an exact criterion:

  `(∀ c, r_t(c) is even)  ⟺  2t ∈ L and t ∉ L`.

This file proves the `⟸` direction **in full generality** — for an arbitrary rational
positive-semidefinite-free setting, in fact for an arbitrary rational matrix `B`, with no
minimality, positivity or symmetry hypothesis at all — and settles the `⟹` direction in
rank one, where the criterion becomes a theorem.

* `halfPt_multiplicity_even_of_primitive` : the hypothesis "`v` is shortest" in
  `halfPt_multiplicity_even` is superfluous; all that the antipodal involution `m ↦ v - m`
  needs is `v ∉ 2L`.
* `two_torsion_multiplicity_even` : consequently every coefficient is even whenever `2t ∈ L`
  and `t ∉ L`.  This closes the `⟸` half of Conjecture 2.
* `rank_one_multiplicity_odd_of_not_half` : in rank one, if `2t ∉ ℤ` then the coefficient at
  `c = t²` equals `1`, so it is odd.
* `rank_one_multiplicity_even_iff` : **Conjecture 2 in rank one**, an exact `iff`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): evenness of the shifted theta coefficients is equivalent to the
existence of the antipodal symmetry, i.e. to `2t ∈ L, t ∉ L`; no other mechanism can force it.
Experiment (Experimenter): stripping `hv : Q(v) = λ₁` from `halfPt_multiplicity_even` leaves a
proof that uses only `v - 2m ≠ 0`, so the `⟸` direction holds for every `2`-torsion shift.
For `⟹`, the rank-one computation is decisive: `(t - m)² = (t - m')²` with `m ≠ m'` forces
`m + m' = 2t`, so `2t ∉ ℤ` makes *every* coefficient at most `1`, and the coefficient at
`c = t²` is exactly `1`.
Analysis (Analyst): the obstruction to a rank-`n` proof of `⟹` is that a coefficient can be
even "by accident" (two unrelated pairs of lattice points at the same distance); the rank-one
argument works because the fibre of `x ↦ Q(x)` over `c` has at most two points.  So the
general `⟹` is "true but hard", needing a global count rather than a fibrewise one.
Critique (Critic): `rank_one_multiplicity_even_iff` is an honest `iff` with no side condition,
and its two halves are proved by genuinely different arguments (involution vs. fibre count);
`two_torsion_multiplicity_even` is strictly stronger than the cycle-2 theorem, which it
re-derives (`halfPt_multiplicity_even_reproved`).
Synthesis (PI): the parity of the shifted theta series is an exact `2`-torsion criterion in
rank one, and the sufficiency half holds in every rank.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## Evenness without minimality -/






/-! ## Rank one: the criterion is exact -/





open DiophantineLattice in
theorem solution(B : Matrix (Fin n) (Fin n) ℚ) {v : Fin n → ℤ}
    (hv2 : ∀ m : Fin n → ℤ, (fun i => v i - 2 * m i) ≠ 0) (c : ℚ) (S : Finset (Fin n → ℤ))
    (hS : ∀ m : Fin n → ℤ, m ∈ S ↔ form B (fun i => halfPt v i - emb m i) = c) :
    Even S.card := by
  classical
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
    exact hv2 m (funext hvm)
  have hsum : ∑ _x ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => g a) (fun a _ => by decide)
      (fun a ha _ => hgfix a ha) (fun a ha => hgmem a ha) (fun a _ => hginv a)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum
