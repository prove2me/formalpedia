-- Prove2me | solution 1 for BonferroniMarginals.fisher_type_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:25:47.224723+00:00
-- url     : https://prove2.me/submissions/f43b804b-c7f7-4b91-a92f-dba5e90be1f9

-- Sol generated from MachineLearning/BonferroniMarginals/Corradi.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_card_cover_corradi

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


/-- Truncated-subtraction bookkeeping. -/
lemma nat_sub_le_sub_of_add_le {a b c d : ℕ} (h : a + d ≤ c + b) (hd : d ≤ c) :
    a - b ≤ c - d := by omega

/-! ## Corrádi's inequality -/



/-! ## Sharpness at both ends of the correlation scale -/



/-! ## The machine-learning corollary -/




open BonferroniMarginals in
theorem solution[DecidableEq ι] {m t : ℕ}
    (hm : ∀ i ∈ I, m ≤ (A i).card)
    (ht : ∀ p ∈ I.offDiag, (A p.1 ∩ A p.2).card ≤ t)
    (htm : t ≤ m) :
    I.card * (m ^ 2 - (cover I A).card * t)
      ≤ (cover I A).card * (m - t) := by
  classical
  set k := I.card with hk
  set N := (cover I A).card with hN
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  have hmain := card_cover_corradi (I := I) (A := A) hm ht
  rw [← hk, ← hN] at hmain
  -- `k m² ≤ N (m + (k-1) t) = N m + k (N t) − N t`
  have hexp : N * (m + (k - 1) * t) + N * t = N * m + k * (N * t) := by
    have hk1 : k - 1 + 1 = k := by omega
    calc N * (m + (k - 1) * t) + N * t = N * m + ((k - 1) + 1) * (N * t) := by ring
      _ = N * m + k * (N * t) := by rw [hk1]
  have hadd : k * m ^ 2 + N * t ≤ N * m + k * (N * t) := by
    calc k * m ^ 2 + N * t ≤ N * (m + (k - 1) * t) + N * t :=
          Nat.add_le_add_right hmain _
      _ = N * m + k * (N * t) := hexp
  have e1 : k * (m ^ 2 - N * t) = k * m ^ 2 - k * (N * t) := by rw [Nat.mul_sub]
  have e2 : N * (m - t) = N * m - N * t := by rw [Nat.mul_sub]
  rw [e1, e2]
  exact nat_sub_le_sub_of_add_le hadd (Nat.mul_le_mul_left N htm)
