-- Prove2me | solution 1 for KleberSplit.parts_union_eq_of_msym_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:07:59.277927+00:00
-- url     : https://prove2.me/submissions/bb87acd2-aa63-4e38-897c-4b99a5d70c2f

-- Sol generated from Algebra/KleberComplementaryProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Theorems.Thm_KleberSplit_Qstat_add
import Theorems.Thm_KleberSplit_Qstat_of_mem_orbit
import Theorems.Thm_KleberSplit_coeff_msym
import Theorems.Thm_KleberSplit_dotp_eq_zero_iff
import Theorems.Thm_KleberSplit_equivMapDomain_mem_orbit
import Theorems.Thm_KleberSplit_exists_placement_avoiding
import Theorems.Thm_KleberSplit_parts_add_of_disjoint
import Theorems.Thm_KleberSplit_parts_of_mem_orbit
import Theorems.Thm_KleberSplit_support_equivMapDomain
/-
# Complementary products of monomial symmetric functions

This file develops, from scratch inside `MvPolynomial (Fin N) R`, the theory needed to
attack the *componentwise splitting independence* phenomenon studied in the paper
"Kleber's conjecture and complementary products of symmetric functions":

> for a partition `θ`, the products `s_α s_β` are linearly independent as `{α, β}` ranges
> over unordered pairs of partitions with `α + β = θ`,

together with its stated analogue for **monomial** symmetric functions over fields of
characteristic zero and over `ℤ`.

Mathlib has no ring of symmetric functions and no Schur functions, so everything here is
built by hand.  We work with *monomial symmetric polynomials* `msym R d`, the sum of all
distinct permutations of a monomial `x^d` in `N` variables; these are exactly the monomial
symmetric functions `m_λ` when `N` is at least the number of parts involved.

## Main results

* `KleberSplit.linearIndependent_msym_mul`: if `{α_i, β_i}` is a finite family of pairs of
  exponent vectors whose *multiset unions* `parts α_i + parts β_i` are pairwise distinct
  (and which fit into `N` variables), then the products `m_{α_i} m_{β_i}` are linearly
  independent over any characteristic-zero domain (in particular over `ℤ` and over any
  field of characteristic zero).
* `KleberSplit.linearIndependent_msym_complementary`: the specialisation to
  componentwise splittings `α_i + β_i = θ` of a fixed `θ`.
* `KleberSplit.linearIndependent_msym`: the monomial symmetric polynomials themselves are
  linearly independent (the case `β = 0`).
* `KleberSplit.linearIndependent_kleber_complementary`: the Kleber-style form, for
  complementary pairs `(λ, ρ - λ)` inside a fixed shape `ρ` (e.g. a rectangle), where the
  hypothesis that the variables suffice is derived rather than assumed.
* `KleberSplit.linearIndependent_row_splittings`: the full one-row case
  `θ = (n)`: the products `m_{(k)} m_{(n-k)}`, `2 * k ≤ n`, are linearly independent.
* `KleberSplit.parts_union_eq_of_msym_mul_eq`: a product `m_α m_β` determines the multiset
  union `parts α + parts β`.
* `KleberSplit.not_linearIndependent_of_too_few_variables` and
  `KleberSplit.linearIndependent_collision_pair_two` (with its special case
  `KleberSplit.linearIndependent_collision_pair`): the two hypotheses are, respectively,
  necessary and not necessary.

The generalisation to products of arbitrarily many factors is in
`Algebra.KleberManyFoldProducts`.

## The mechanism

The Schur-function proof cannot use the dominance-leading term of `s_α s_β`, since every
splitting of `θ` has the *same* leading term `s_θ`.  The mechanism isolated here is the
opposite end of the expansion, controlled by the quadratic statistic
`Qstat d = ∑ i, (d i)^2`:

* `Qstat (u + v) = Qstat u + Qstat v + 2 * dotp u v` (`Qstat_add`), so any monomial
  occurring in `m_α m_β` has `Qstat` **at least** `Qstat α + Qstat β`;
* equality holds exactly when the two exponent vectors have disjoint supports
  (`dotp_eq_zero_iff`), in which case the resulting monomial has part multiset
  `parts α + parts β`, the multiset union.

So the `Qstat`-minimal monomials of `m_α m_β` remember precisely the multiset union of
`α` and `β`, which yields a genuine (non-dominance) triangularity argument.

## Boundary

The hypothesis that the unions are distinct is *not* automatic for componentwise
splittings: `KleberSplit.union_collision_five_three` exhibits two distinct splittings of
`θ = (5,3)` with the same union.  This is exactly the obstruction that makes the full
theorem of the paper hard, and it is recorded here honestly rather than hidden.
-/


open KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ}


/-! ### Parts, orbits and the quadratic statistic -/





lemma self_mem_orbit (d : Exp N) : d ∈ orbit d :=
  Finset.mem_image.2 ⟨Equiv.refl _, Finset.mem_univ _, by simp⟩



lemma parts_equivMapDomain (e : Equiv.Perm (Fin N)) (d : Exp N) :
    parts (Finsupp.equivMapDomain e d) = parts d := by
  unfold parts
  rw [support_equivMapDomain]
  simp [Finset.map_val, Multiset.map_map, Function.comp]

lemma Qstat_equivMapDomain (e : Equiv.Perm (Fin N)) (d : Exp N) :
    Qstat (Finsupp.equivMapDomain e d) = Qstat d := by
  unfold Qstat
  rw [← Equiv.sum_comp e (fun i => ((Finsupp.equivMapDomain e d) i) ^ 2)]
  simp [Finsupp.equivMapDomain_apply]







lemma exists_disjoint_placement (a b : Exp N)
    (h : a.support.card + b.support.card ≤ N) :
    ∃ e : Equiv.Perm (Fin N), Disjoint a.support (Finsupp.equivMapDomain e b).support :=
  exists_placement_avoiding a.support b h

/-! ### Monomial symmetric polynomials -/


variable {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]


/-- The coefficients of a product of two monomial symmetric polynomials are the counts of
the ways of splitting the monomial. -/
lemma coeff_msym_mul (a b w : Exp N) :
    MvPolynomial.coeff w (msym S a * msym S b)
      = (((Finset.antidiagonal w).filter
          (fun x : Exp N × Exp N => x.1 ∈ orbit a ∧ x.2 ∈ orbit b)).card : S) := by
  rw [MvPolynomial.coeff_mul, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_msym, coeff_msym]
  by_cases h1 : x.1 ∈ orbit a <;> by_cases h2 : x.2 ∈ orbit b <;> simp [h1, h2]

/-- A monomial occurring in `m_a * m_b` really is a sum of a rearrangement of `a` and a
rearrangement of `b`. -/
lemma exists_split_of_coeff_ne_zero {a b w : Exp N}
    (h : MvPolynomial.coeff w (msym S a * msym S b) ≠ 0) :
    ∃ u ∈ orbit a, ∃ v ∈ orbit b, u + v = w := by
  rw [coeff_msym_mul] at h
  have hcard : (((Finset.antidiagonal w).filter
      (fun x : Exp N × Exp N => x.1 ∈ orbit a ∧ x.2 ∈ orbit b)).card) ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.1 hcard
  rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
  exact ⟨x.1, hx.2.1, x.2, hx.2.2, hx.1⟩

/-- Any monomial of the form `u + v` with `u` a rearrangement of `a` and `v` a
rearrangement of `b` really occurs in `m_a * m_b` (over a characteristic-zero ring). -/
lemma coeff_add_mem_orbit_ne_zero [CharZero S] {a b u v : Exp N}
    (hu : u ∈ orbit a) (hv : v ∈ orbit b) :
    MvPolynomial.coeff (u + v) (msym S a * msym S b) ≠ 0 := by
  classical
  set w := u + v with hw
  rw [coeff_msym_mul]
  have hne : (((Finset.antidiagonal w).filter
      (fun x : Exp N × Exp N => x.1 ∈ orbit a ∧ x.2 ∈ orbit b))).Nonempty := by
    refine ⟨(u, v), ?_⟩
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    exact ⟨rfl, hu, hv⟩
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hne)

/-! ### The independence theorem -/










/-! ### The one-row case, unconditionally -/



/-! ### The boundary: unions can collide -/


/-! ### The product determines the multiset union -/


/-! ### Sharpness: enough variables are needed -/




/-! ### Beyond the criterion: the smallest collision class -/





open KleberSplit in
theorem solution[CharZero R] {a b a' b' : Exp N}
    (hcard : a.support.card + b.support.card ≤ N)
    (hcard' : a'.support.card + b'.support.card ≤ N)
    (h : msym R a * msym R b = msym R a' * msym R b') :
    parts a + parts b = parts a' + parts b' := by
  obtain ⟨e, he⟩ := exists_disjoint_placement a b hcard
  obtain ⟨e', he'⟩ := exists_disjoint_placement a' b' hcard'
  set w : Exp N := a + Finsupp.equivMapDomain e b with hw
  set w' : Exp N := a' + Finsupp.equivMapDomain e' b' with hw'
  have hQw : Qstat w = Qstat a + Qstat b := by
    rw [hw, Qstat_add, (dotp_eq_zero_iff _ _).2 he, Qstat_equivMapDomain]; omega
  have hQw' : Qstat w' = Qstat a' + Qstat b' := by
    rw [hw', Qstat_add, (dotp_eq_zero_iff _ _).2 he', Qstat_equivMapDomain]; omega
  have hpw : parts w = parts a + parts b := by
    rw [hw, parts_add_of_disjoint he, parts_equivMapDomain]
  -- the chosen monomial of one product occurs in the other
  have hne : MvPolynomial.coeff w (msym R a' * msym R b') ≠ 0 := by
    rw [← h]
    exact coeff_add_mem_orbit_ne_zero (self_mem_orbit _) (equivMapDomain_mem_orbit e b)
  have hne' : MvPolynomial.coeff w' (msym R a * msym R b) ≠ 0 := by
    rw [h]
    exact coeff_add_mem_orbit_ne_zero (self_mem_orbit _) (equivMapDomain_mem_orbit e' b')
  obtain ⟨u, hu, v, hv, huv⟩ := exists_split_of_coeff_ne_zero hne
  obtain ⟨u', hu', v', hv', huv'⟩ := exists_split_of_coeff_ne_zero hne'
  have hQ1 : Qstat w = Qstat a' + Qstat b' + 2 * dotp u v := by
    rw [← huv, Qstat_add, Qstat_of_mem_orbit hu, Qstat_of_mem_orbit hv]
  have hQ2 : Qstat w' = Qstat a + Qstat b + 2 * dotp u' v' := by
    rw [← huv', Qstat_add, Qstat_of_mem_orbit hu', Qstat_of_mem_orbit hv']
  have hdot : dotp u v = 0 := by omega
  have hdisj : Disjoint u.support v.support := (dotp_eq_zero_iff u v).1 hdot
  rw [← hpw, ← huv, parts_add_of_disjoint hdisj, parts_of_mem_orbit hu, parts_of_mem_orbit hv]
