-- Prove2me | solution 1 for IRV.irvWinnerOn_stable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:11:12.615425+00:00
-- url     : https://prove2.me/submissions/a915ea5d-8d28-4767-8610-59c63b124be6

-- Sol generated from Bridges/IRVStability.lean
import Mathlib
import Definitions.Def_Bridges_IRVStability
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL3 Tropical Satake Certified Robustness for IRV Classifiers

This file formalizes a robustness theory for deterministic, tie-free
instant-runoff / sequential-elimination classifiers built from multiclass
tropical score maps.

## Main results

* `roundLoser_eq_of_strict_min` — uniqueness of the minimizer on a finite set
* `gap_preserved_under_perturbation` — the one-round perturbation lemma
* `eliminationOrderOn_stable` — elimination-order stability under bounded perturbation
* `irvWinnerOn_stable` — winner stability under bounded perturbation
* `irvWinner_certified_robust` — the full tropical/Lipschitz robustness corollary

## Proof architecture

The core theorem proceeds by induction on the cardinality of the active
candidate set. At each round, the gap certificate ensures the current loser
has score at least γ below every other active candidate. A uniform
perturbation of size ≤ ε shifts each score by at most ε, so the gap shrinks
by at most 2ε. When 2ε < γ, the same candidate remains the unique loser,
and the induction carries through the remaining rounds.
-/


open IRV

open Finset

/-! ## Part 1: Core Definitions -/




/-! ## Part 2: Properties of `roundLoser` -/


lemma roundLoser_le {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (v : Fin m → ℝ) : ∀ j ∈ S, v (roundLoser S hS v) ≤ v j :=
  (S.exists_min_image v hS).choose_spec.2

/-
If `i ∈ S` is strictly below every other element of `S` under `v`,
    then `roundLoser S hS v = i`.
-/
lemma roundLoser_eq_of_strict_min {m : ℕ} {S : Finset (Fin m)} {hS : S.Nonempty}
    {v : Fin m → ℝ} {i : Fin m}
    (hi : i ∈ S) (hmin : ∀ j ∈ S, j ≠ i → v i < v j) :
    roundLoser S hS v = i := by
  -- Since `roundLoser S hS v` is in `S` and `v i < v j` for all `j ∈ S \ {i}`, it must be that `roundLoser S hS v = i`.
  have h_unique_min : ∀ j ∈ S, v j < v (roundLoser S hS v) → False := by
    exact fun j hj => not_lt_of_ge ( roundLoser_le S hS v j hj );
  exact Classical.not_not.1 fun h => h_unique_min i hi <| hmin _ ( roundLoser_mem _ hS _ ) h

/-! ## Part 3: Recursive Elimination -/







/-! ## Part 4: One-Round Perturbation Lemma -/

/-
The algebraic heart: if `i` has gap `γ` in `S` under `v`, and `v'` is
    within `ε` of `v` coordinatewise, then `i` still has gap `γ - 2*ε`
    in `S` under `v'`.
-/

/-
From a preserved positive gap, the same candidate is the strict minimizer.
-/

/-! ## Part 5: Main Stability Theorem -/

/-
**Elimination-order stability theorem.** If the elimination of `v` on `S`
    is gap-certified with parameter `γ`, and `v'` is within `ε` of `v`
    coordinatewise with `2ε < γ`, then the elimination order of `v'` on `S`
    equals that of `v`.
-/

/-! ## Part 6: Winner Stability -/

/-
**Winner stability theorem.** Under the same hypotheses as
    `eliminationOrderOn_stable`, the IRV winner is preserved.
-/

/-
Winner stability on the full candidate set.
-/

/-! ## Part 7: Tropical / GL3 Certified Robustness Corollary -/

/-
**Tropical/GL3 certified robustness theorem.** If a score map `s` is
    K-Lipschitz in L∞ (in the sense that coordinatewise perturbation ≤ r
    implies score perturbation ≤ K*r), and the elimination of `s x` on all
    candidates is gap-certified with parameter `γ`, then any input `x'`
    within L∞-radius `r` of `x` yields the same IRV winner, provided
    `2 K r < γ`.
-/


open IRV in
theorem solution{m : ℕ}
    {v v' : Fin m → ℝ}
    (S : Finset (Fin m)) (hS : S.Nonempty)
    {ε γ : ℝ}
    (hcert : EliminationGapCertified S hS v γ)
    (hε : 0 ≤ ε)
    (hgap : 2 * ε < γ)
    (hclose : ∀ i, |v' i - v i| ≤ ε) :
    irvWinnerOn S hS v' = irvWinnerOn S hS v := by
  classical
  have hγpos : 0 < γ := by linarith
  have hround_v : ∀ (T : Finset (Fin m)) (hT : T.Nonempty) (i : Fin m),
      i ∈ T → (∀ j ∈ T, j ≠ i → v i + γ ≤ v j) → roundLoser T hT v = i := by
    intro T hT i hiT hg
    by_contra hne
    have hm : roundLoser T hT v ∈ T := roundLoser_mem T hT v
    have hmin : ∀ j ∈ T, v (roundLoser T hT v) ≤ v j :=
      (T.exists_min_image v hT).choose_spec.2
    have h1 : v i + γ ≤ v (roundLoser T hT v) := hg _ hm hne
    have h2 : v (roundLoser T hT v) ≤ v i := hmin i hiT
    linarith
  have hround_v' : ∀ (T : Finset (Fin m)) (hT : T.Nonempty) (i : Fin m),
      i ∈ T → (∀ j ∈ T, j ≠ i → v i + γ ≤ v j) → roundLoser T hT v' = i := by
    intro T hT i hiT hg
    by_contra hne
    have hm : roundLoser T hT v' ∈ T := roundLoser_mem T hT v'
    have hmin : ∀ j ∈ T, v' (roundLoser T hT v') ≤ v' j :=
      (T.exists_min_image v' hT).choose_spec.2
    have hvi : v' i ≤ v i + ε := by have := abs_le.mp (hclose i); linarith
    have hvj : ∀ j ∈ T, j ≠ i → v j - ε ≤ v' j := by
      intro j hj hji
      have := abs_le.mp (hclose j)
      linarith [hg j hj hji]
    have h6 := hvj (roundLoser T hT v') hm hne
    have h7 : v i + 2 * ε < v (roundLoser T hT v') := by
      have h8 := hg (roundLoser T hT v') hm hne
      linarith
    have h9 := hmin i hiT
    linarith
  have irv_dite : ∀ (T : Finset (Fin m)) (hT : T.Nonempty) (u : Fin m → ℝ) (i : Fin m)
      (hne : (T.erase i).Nonempty), ¬(T.card ≤ 1) → i = roundLoser T hT u →
      irvWinnerOn T hT u = irvWinnerOn (T.erase i) hne u := by
    intro T hT u i hne hc hie
    subst hie
    conv_lhs => unfold irvWinnerOn
    split
    · exact absurd ‹T.card ≤ 1› hc
    · have hp : (T.erase (roundLoser T hT u)).Nonempty := by
        by_contra h0
        have h0' : (T.erase (roundLoser T hT u)) = ∅ :=
          Finset.eq_empty_of_forall_notMem fun a ha => h0 ⟨a, ha⟩
        have h2 : T.card ≤ 1 := by
          have h3 : T ⊆ {roundLoser T hT u} := fun a ha => by
            by_contra haj
            exact Finset.eq_empty_iff_forall_notMem.mp h0' a
              (Finset.mem_erase.mpr ⟨fun hh => haj (by subst hh; exact Finset.mem_singleton_self _),
                ha⟩)
          simpa using Finset.card_le_card h3
        omega
      exact congrArg (fun h : (T.erase (roundLoser T hT u)).Nonempty =>
        irvWinnerOn (T.erase (roundLoser T hT u)) h u) (Subsingleton.elim hp hne)

  have main : ∀ n : ℕ, ∀ (T : Finset (Fin m)) (hT : T.Nonempty),
      EliminationGapCertified T hT v γ → T.card = n →
      irvWinnerOn T hT v' = irvWinnerOn T hT v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hT hcert hcard
      by_cases hc1 : T.card ≤ 1
      · have e1 : irvWinnerOn T hT v' = T.min' hT := by
          unfold irvWinnerOn; split
          · rfl
          · exact absurd hc1 (by assumption)
        have e2 : irvWinnerOn T hT v = T.min' hT := by
          unfold irvWinnerOn; split
          · rfl
          · exact absurd hc1 (by assumption)
        rw [e1, e2]
      · unfold EliminationGapCertified at hcert
        split at hcert
        · exact absurd ‹T.card ≤ 1› hc1
        · obtain ⟨hgapH, hcert'⟩ := hcert
          obtain ⟨hiT, hgapS⟩ := hgapH
          have hloser' : roundLoser T hT v' = roundLoser T hT v :=
            hround_v' T hT _ hiT hgapS
          have hlt : (T.erase (roundLoser T hT v)).card < n := by
            have hlt0 : (T.erase (roundLoser T hT v)).card < T.card :=
              Finset.card_erase_lt_of_mem hiT
            rw [hcard] at hlt0
            exact hlt0
          have hne : (T.erase (roundLoser T hT v)).Nonempty := by
            by_contra h0
            have h0' : (T.erase (roundLoser T hT v)) = ∅ :=
              Finset.eq_empty_of_forall_notMem fun a ha => h0 ⟨a, ha⟩
            have h2 : T.card ≤ 1 := by
              have h3 : T ⊆ {roundLoser T hT v} := fun a ha => by
                by_contra haj
                exact Finset.eq_empty_iff_forall_notMem.mp h0' a
                  (Finset.mem_erase.mpr ⟨fun hh => haj (by subst hh; exact Finset.mem_singleton_self _),
                    ha⟩)
              simpa using Finset.card_le_card h3
            omega
          have hcert2 : EliminationGapCertified (T.erase (roundLoser T hT v))
              hne v γ := hcert'
          rw [irv_dite T hT v' (roundLoser T hT v) hne hc1 hloser'.symm,
            irv_dite T hT v (roundLoser T hT v) hne hc1 rfl]
          exact ih _ hlt (T.erase (roundLoser T hT v)) hne hcert2 rfl
  exact main S.card S hS hcert rfl
