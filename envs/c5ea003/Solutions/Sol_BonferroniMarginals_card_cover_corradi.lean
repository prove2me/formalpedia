-- Prove2me | solution 1 for BonferroniMarginals.card_cover_corradi
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:50.111851+00:00
-- url     : https://prove2.me/submissions/1ba82668-7664-42d4-a406-2d833f32dfd6

-- Sol generated from MachineLearning/BonferroniMarginals/Corradi.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_sq_le_mul_add_of_le
import Theorems.Thm_BonferroniMarginals_sq_sum_card_le_card_cover_mul_sum_prod
import Theorems.Thm_BonferroniMarginals_sum_prod_eq_sum_card_add_offDiag

/-!
# Which marginals? The Corrádi bound and the Fisher-type consequence

`Core.lean` develops the Bonferroni machinery for an *arbitrary* finite family;
the content of the conjecture is therefore entirely in **which marginals are fed
into it**.  This file feeds in the two standard hypotheses of design theory and
of ensemble learning:

* a uniform lower bound `m ≤ |Aᵢ|` on the **first** marginals, and
* a uniform upper bound `|Aᵢ ∩ Aⱼ| ≤ t` (`i ≠ j`) on the **second** marginals,

and extracts the sharp conclusions.

Main results.

* `card_cover_corradi` — **Corrádi's inequality**, division-free:
  `k·m² ≤ |cover| · (m + (k−1)·t)`, where `k` is the number of sets.
  Equivalently `|⋃ᵢ Aᵢ| ≥ k m² / (m + (k−1) t)`.
* `fisher_type_bound` — turning the same data around: if the ambient union is
  small (`N·t < m²`) then the *number of sets* is bounded,
  `k · (m² − N·t) ≤ N · (m − t)`.  This is the counting principle behind Fisher's
  inequality and behind Plotkin-type bounds in coding theory.
* `corradi_tight_of_pairwiseDisjoint`, `corradi_tight_of_constant` — the bound is
  attained at *both* extremes of the correlation scale (`t = 0` partitions and
  `t = m` totally correlated families), so no better bound is expressible in the
  marginal data `(k, m, t)` alone.
* `ensemble_coverage_bound` — the machine-learning reading: `k` hypotheses each
  failing on at least `m` of `N` samples, with pairwise co-failure at most `t`,
  must jointly fail on many distinct samples.

The proof route is: `sq_sum_card_le_card_cover_mul_sum_prod` (Cauchy–Schwarz on
the multiplicity function) + monotonicity of `S ↦ S²/(S+c)` + the marginal
hypotheses.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Two arithmetic lemmas -/



/-! ## Corrádi's inequality -/



/-! ## Sharpness at both ends of the correlation scale -/



/-! ## The machine-learning corollary -/




open BonferroniMarginals in
theorem solution[DecidableEq ι] {m t : ℕ}
    (hm : ∀ i ∈ I, m ≤ (A i).card)
    (ht : ∀ p ∈ I.offDiag, (A p.1 ∩ A p.2).card ≤ t) :
    I.card * m ^ 2 ≤ (cover I A).card * (m + (I.card - 1) * t) := by
  classical
  set k := I.card with hk
  set N := (cover I A).card with hN
  set S := ∑ i ∈ I, (A i).card with hS
  -- lower bound on the first marginal mass
  have hSlow : k * m ≤ S := by
    have := Finset.card_nsmul_le_sum I (fun i => (A i).card) m hm
    simpa [hS, hk, mul_comm] using this
  -- upper bound on the pairwise mass
  have hoff : ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card ≤ (k * k - k) * t := by
    have h1 := Finset.sum_le_card_nsmul I.offDiag (fun p => (A p.1 ∩ A p.2).card) t ht
    simpa [Finset.offDiag_card, hk, mul_comm] using h1
  -- Cauchy–Schwarz from the core file
  have hCS := sq_sum_card_le_card_cover_mul_sum_prod I A
  rw [sum_prod_eq_sum_card_add_offDiag] at hCS
  have hCS' : S ^ 2 ≤ N * (S + (k * k - k) * t) := by
    refine le_trans hCS ?_
    exact Nat.mul_le_mul_left N (Nat.add_le_add_left hoff _)
  -- push the bound down from `S` to `k * m`
  have hstep := sq_le_mul_add_of_le hCS' hSlow
  -- unravel: `(k m)² ≤ N (k m + k (k-1) t) = k · N · (m + (k-1) t)`
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · have hfac : k * m + (k * k - k) * t = k * (m + (k - 1) * t) := by
      have : k * k - k = k * (k - 1) := by
        cases k with
        | zero => simp
        | succ n => simp [Nat.mul_succ, Nat.mul_comm]
      rw [this]
      ring
    rw [hfac] at hstep
    have hstep' : k * (k * m ^ 2) ≤ k * (N * (m + (k - 1) * t)) := by
      calc k * (k * m ^ 2) = (k * m) ^ 2 := by ring
        _ ≤ N * (k * (m + (k - 1) * t)) := hstep
        _ = k * (N * (m + (k - 1) * t)) := by ring
    exact Nat.le_of_mul_le_mul_left hstep' hk0
