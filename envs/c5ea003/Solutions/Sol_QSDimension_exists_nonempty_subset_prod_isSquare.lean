-- Prove2me | solution 1 for QSDimension.exists_nonempty_subset_prod_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:12:54.097329+00:00
-- url     : https://prove2.me/submissions/5f2cd4d4-581a-4e72-8edc-25247e2f9fea

-- Sol generated from Shared/QSFactorBaseDimension.lean
import Mathlib
import Definitions.Def_Shared_QSFactorBaseDimension
import Definitions.Def_Shared_QSRelationPoolRandom
import Definitions.Def_Shared_SmoothCountSparsity
import Theorems.Thm_QSDimension_isSquare_of_even_factorization

/-!
# The factor base the relations actually live in, and the `𝔽₂` dimension bound

The measurements of experiment 465 say that the *input statistics* of the
quadratic sieve are those of a random pool.  What is then left as the sieve's
genuine advantage is algorithmic, and this file formalises the two algebraic
facts that constitute it.

1. **The support of a relation is confined to the admissible primes.**  A
   `B`-smooth value `x^2 - N` factors only over primes `p ≤ B` for which `N` is a
   quadratic residue (`smooth_qsValue_support`).  So the exponent vectors of the
   relations do not live in `𝔽₂^{π(B)}` but in the much smaller subspace indexed
   by the admissible primes.

2. **A dimension count then produces a congruence of squares.**  Any family of
   more nonzero naturals than the size of their common support admits a nonempty
   sub-family whose product is a perfect square
   (`exists_nonempty_subset_prod_isSquare`), because their `𝔽₂` exponent vectors
   must be linearly dependent.

Combining the two gives `qs_congruence_of_squares`: `|A| + 1` smooth sieve values
suffice to build a square, where `A` is the set of *admissible* primes — half the
factor base — rather than the whole factor base.  This is the precise sense in
which the quadratic-character constraint, which costs nothing in smoothness
probability (see `Catalog.Shared.QSRelationPoolRandom`), is a *gain* in the
linear-algebra stage.

Main results:

* `isSquare_of_even_factorization` — even exponents means perfect square.
* `exists_nonempty_subset_prod_isSquare` — the `𝔽₂` dependency argument.
* `smooth_qsValue_support` — relations are supported on admissible primes.
* `qs_congruence_of_squares` — end-to-end: `|A| + 1` relations give a square.
-/

open QSDimension

open Finset



/-! ## The quadratic-sieve specialisation -/






open QSDimension in
theorem solution{ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (v : ι → ℕ) (hv : ∀ i, v i ≠ 0)
    (hsupp : ∀ i, ∀ p, (v i).factorization p ≠ 0 → p ∈ S)
    (hcard : S.card < Fintype.card ι) :
    ∃ T : Finset ι, T.Nonempty ∧ IsSquare (∏ i ∈ T, v i) := by
  classical
  set w : ι → (S → ZMod 2) := fun i p => (((v i).factorization p : ℕ) : ZMod 2) with hw
  have hnli : ¬ LinearIndependent (ZMod 2) w := by
    intro hli
    have hb := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hb
    omega
  obtain ⟨g, hgsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnli
  set T : Finset ι := Finset.univ.filter (fun i => g i ≠ 0) with hT
  have hTne : T.Nonempty := ⟨i₀, by simp [hT, hi₀]⟩
  have hg1 : ∀ i ∈ T, g i = 1 := by
    intro i hi
    have : g i ≠ 0 := (Finset.mem_filter.1 hi).2
    revert this
    generalize g i = a
    revert a
    decide
  have hprod_ne : (∏ i ∈ T, v i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 (fun i _ => hv i)
  refine ⟨T, hTne, isSquare_of_even_factorization hprod_ne (fun p => ?_)⟩
  have hfact : (∏ i ∈ T, v i).factorization p = ∑ i ∈ T, (v i).factorization p := by
    rw [Nat.factorization_prod (fun i _ => hv i)]
    simp
  by_cases hpS : p ∈ S
  · -- use the `𝔽₂` dependency at the coordinate `p`
    have hzero : ∑ i : ι, g i * w i ⟨p, hpS⟩ = 0 := by
      have h := congrFun hgsum ⟨p, hpS⟩
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hzeroout : ∀ i ∈ (Finset.univ : Finset ι), i ∉ T → g i * w i ⟨p, hpS⟩ = 0 := by
      intro i _ hiT
      have hgi : g i = 0 := by
        by_contra hc
        exact hiT (Finset.mem_filter.2 ⟨Finset.mem_univ i, hc⟩)
      simp [hgi]
    have hsub : ∑ i ∈ T, (g i * w i ⟨p, hpS⟩) = ∑ i : ι, g i * w i ⟨p, hpS⟩ :=
      Finset.sum_subset (Finset.filter_subset _ _) hzeroout
    have hone : ∑ i ∈ T, (g i * w i ⟨p, hpS⟩) = ∑ i ∈ T, w i ⟨p, hpS⟩ :=
      Finset.sum_congr rfl (fun i hi => by rw [hg1 i hi, one_mul])
    have hsum0 : ((∑ i ∈ T, (v i).factorization p : ℕ) : ZMod 2) = 0 := by
      have : ∑ i ∈ T, w i ⟨p, hpS⟩ = 0 := by rw [← hone, hsub, hzero]
      simpa [hw] using this
    rw [hfact, even_iff_two_dvd, ← ZMod.natCast_eq_zero_iff]
    exact hsum0
  · have : ∀ i ∈ T, (v i).factorization p = 0 := by
      intro i _
      by_contra hcon
      exact hpS (hsupp i p hcon)
    rw [hfact, Finset.sum_congr rfl this]
    simp
