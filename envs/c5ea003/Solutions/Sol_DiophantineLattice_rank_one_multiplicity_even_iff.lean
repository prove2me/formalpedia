-- Prove2me | solution 1 for DiophantineLattice.rank_one_multiplicity_even_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:47:26.41145+00:00
-- url     : https://prove2.me/submissions/3ef0e882-95a2-4f7c-aebc-709b3b8d83a8

-- Sol generated from Novelty/DiophantineLatticeMultiplicity.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Theorems.Thm_DiophantineLattice_halfPt_multiplicity_even_of_primitive
import Theorems.Thm_DiophantineLattice_multiplicity_even_imp_not_lattice
import Theorems.Thm_DiophantineLattice_rank_one_multiplicity_odd_of_not_half
import Theorems.Thm_DiophantineLattice_standard_posDef
import Theorems.Thm_DiophantineLattice_two_torsion_primitive

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


/-- A `2`-torsion shift is literally half of a lattice vector. -/
lemma eq_halfPt_of_two {t : Fin n → ℚ} {v : Fin n → ℤ} (hv : ∀ i, (2 : ℚ) * t i = (v i : ℚ)) :
    t = halfPt v := by
  funext i
  show t i = (v i : ℚ) / 2
  linarith [hv i]


/-- **Conjecture 2, sufficiency (all ranks).**  If `2t` is a lattice vector and `t` is not,
then every coefficient of the shifted theta series of `x ↦ Q(x - t)` is even. -/
theorem two_torsion_multiplicity_even (B : Matrix (Fin n) (Fin n) ℚ) {t : Fin n → ℚ}
    {v : Fin n → ℤ} (hv : ∀ i, (2 : ℚ) * t i = (v i : ℚ)) (hnl : ∀ k : Fin n → ℤ, t ≠ emb k)
    (c : ℚ) (S : Finset (Fin n → ℤ))
    (hS : ∀ m : Fin n → ℤ, m ∈ S ↔ form B (fun i => t i - emb m i) = c) :
    Even S.card := by
  have hprim := two_torsion_primitive hv hnl
  rw [eq_halfPt_of_two hv] at hS
  exact halfPt_multiplicity_even_of_primitive B hprim c S hS


/-! ## Rank one: the criterion is exact -/





open DiophantineLattice in
theorem solution(t : Fin 1 → ℚ) :
    (∀ (c : ℚ) (S : Finset (Fin 1 → ℤ)),
        (∀ m : Fin 1 → ℤ, m ∈ S ↔ form (1 : Matrix (Fin 1) (Fin 1) ℚ)
          (fun i => t i - emb m i) = c) → Even S.card)
      ↔ ((∃ v : Fin 1 → ℤ, ∀ i, (2 : ℚ) * t i = (v i : ℚ)) ∧ ∀ k : Fin 1 → ℤ, t ≠ emb k) := by
  constructor
  · intro heven
    refine ⟨?_, multiplicity_even_imp_not_lattice standard_posDef heven⟩
    by_contra hno
    push_neg at hno
    have h2 : ∀ k : Fin 1 → ℤ, (fun i => (2 : ℚ) * t i) ≠ emb k := by
      intro k hk
      obtain ⟨i, hi⟩ := hno k
      exact hi (congrFun hk i)
    obtain ⟨c, S, hS, hodd⟩ := rank_one_multiplicity_odd_of_not_half h2
    exact hodd (heven c S hS)
  · rintro ⟨⟨v, hv⟩, hnl⟩ c S hS
    exact two_torsion_multiplicity_even _ hv hnl c S hS
