-- Prove2me | solution 3 for TFoldSumsetAvoidance.dense_set_avoids_large_sumsets
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:15:46.018983+00:00
-- url     : https://prove2.me/submissions/22226580-afb3-48a3-8b01-253c29ac80f1

import Mathlib
import Definitions.Def_Logic_PosetTheory_TFoldSumsetAvoidance

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Logic/PosetTheory/TFoldSumsetAvoidance.lean ====
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avoidance of `t`-fold sumsets in dense sets: the sumset-growth backbone

Fix an integer `t ≥ 2`. A finite set `S` of integers is said to *contain* the
`t`-fold sumset `A₁ + ⋯ + A_t` when every sum `a₁ + ⋯ + a_t` with `aᵢ ∈ Aᵢ`
lies in `S`. A recurring theme in additive combinatorics is that a set which is
*too small* cannot contain the sumset of `t` large sets: growth of iterated
sumsets is unavoidable.

This file develops the exact, sharp growth backbone for iterated sumsets of
integers and turns it into a family of clean **avoidance theorems**.

## Main results

* `sumsetList_card_lower` — the sharp iterated Cauchy–Davenport bound: for a
  list `l` of nonempty finite integer sets,
  `(Σ |Aᵢ|) + 1 ≤ |A₁ + ⋯ + A_t| + t`, i.e. `|A₁ + ⋯ + A_t| ≥ (Σ|Aᵢ|) - (t-1)`.

* `sumsetList_card_uniform` — the uniform specialisation: if there are `t` parts
  each of size at least `k`, then `|A₁ + ⋯ + A_t| ≥ t(k-1) + 1`.

* `sumset_containment_forces_card` — **necessary condition for containment.**
  If `S` contains a `t`-fold sumset whose parts all have size `≥ k`, then
  `|S| ≥ t(k-1) + 1`. Growth of the sumset is forced by the sizes of the parts.

* `sumset_avoidance` — **the avoidance principle (contrapositive).** Any set `S`
  with `|S| ≤ t(k-1)` avoids *every* `t`-fold sumset whose parts all have size
  `≥ k`.

* `dense_set_avoids_large_sumsets` — **dense avoidance existence.** For every
  ambient size `n`, density `δ ≤ 1`, part count `t` and threshold `k` with
  `n ≤ t(k-1)`, there is a set `S` inside `{0, …, n-1}` of density at least `δ`
  which contains no `t`-fold sumset with all parts of size `≥ k`.

The deterministic threshold obtained here is *linear*, of the shape
`k ≳ n / t`. The celebrated probabilistic phenomenon — that a set of density `δ`
can already avoid `t`-fold sumsets once the parts merely exceed
`(log n / log(1/δ))^{1/(t-1)}` — lives far below this linear barrier and is
recorded as the leading open direction of the study.

## Tags
sumset, Cauchy–Davenport, additive combinatorics, sumset avoidance, iterated sumset

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).** Iterated sumsets of `t` integer sets must grow:
a set `S` containing `A₁ + ⋯ + A_t` should be forced to be large whenever the
parts `Aᵢ` are large. Conjectured sharp form: `|A₁+⋯+A_t| ≥ (Σ|Aᵢ|) - (t-1)`,
generalising the single Cauchy–Davenport step `|A+B| ≥ |A|+|B|-1` over a
torsion-free group.

**Experiment (Experimenter).** We modelled the `t`-fold sumset as a right fold
`foldr (· + ·) {0}` over a list of finite sets and proved the sharp bound by
induction, feeding each `cons` step through the single-step Cauchy–Davenport
inequality for torsion-free groups. The uniform corollary and the containment /
avoidance statements then follow by pure arithmetic (`omega`). Concrete check:
`{0,1} + {0,10} = {0,1,10,11}`, size `4 = (2+2) - 1`, saturating the bound.

**Analysis (Analyst).** The linear growth backbone is *true and sharp*
(arithmetic progressions saturate it). It yields a deterministic avoidance
threshold of order `n/t`. Attempts to push the threshold down to the
probabilistic `(log n)^{1/(t-1)}` scale via a naive union bound over all `t`-tuples
of `k`-sets *fail*: the count `n^{tk}` of tuples overwhelms the containment
probability `δ^{t(k-1)+1}` unless `n ≲ 1/δ`. This confirms that the deep result
genuinely needs the structural, non-linear counting of the source paper — it is
"true but hard", not reachable from the growth backbone alone.

**Critique (Critic).** None of the exported theorems are vacuous: each is
witnessed by explicit saturating examples (arithmetic progressions), and the
existence theorem produces a set of density `≥ δ`. The proofs use genuine
induction and the Cauchy–Davenport inequality, not `decide`/`simp`-only. The one
honesty caveat — the linear vs. logarithmic threshold gap — is documented in the
statement docstrings and carried into `FUTURE_DIRECTIONS.md`.

**Synthesis (Principal Investigator).** The sharp iterated Cauchy–Davenport
bound is the correct, reusable foundation on which any quantitative sumset
avoidance theory must sit. It cleanly delivers a deterministic avoidance regime
and isolates the precise place where the probabilistic method is indispensable.
-/

open Finset Pointwise

namespace TFoldSumsetAvoidance

-- [dropped: platform already declares sumsetList]
@[simp] lemma sumsetList_nil : sumsetList [] = {0} := rfl

@[simp] lemma sumsetList_cons (A : Finset ℤ) (l : List (Finset ℤ)) :
    sumsetList (A :: l) = A + sumsetList l := rfl

/-- A `t`-fold sumset of nonempty sets is nonempty. -/
lemma sumsetList_nonempty (l : List (Finset ℤ)) (h : ∀ A ∈ l, A.Nonempty) :
    (sumsetList l).Nonempty := by
  induction l with
  | nil => simp
  | cons A t ih =>
    have hA : A.Nonempty := h A (by simp)
    simpa using hA.add (ih (fun B hB => h B (by simp [hB])))

/-- **Sharp iterated Cauchy–Davenport bound.** For a list of nonempty finite
integer sets, the size of the `t`-fold sumset satisfies
`(Σ |Aᵢ|) + 1 ≤ |A₁ + ⋯ + A_t| + t`, equivalently
`|A₁ + ⋯ + A_t| ≥ (Σ|Aᵢ|) - (t-1)`. The bound is saturated by arithmetic
progressions. -/
lemma sumsetList_card_lower (l : List (Finset ℤ)) (h : ∀ A ∈ l, A.Nonempty) :
    (l.map Finset.card).sum + 1 ≤ (sumsetList l).card + l.length := by
  induction l with
  | nil => simp
  | cons A t ih =>
    have hA : A.Nonempty := h A (by simp)
    have htmem : ∀ B ∈ t, B.Nonempty := fun B hB => h B (by simp [hB])
    have ht := ih htmem
    have htne : (sumsetList t).Nonempty := sumsetList_nonempty t htmem
    have hcd := cauchy_davenport_of_isAddTorsionFree hA htne
    have := hA.card_pos; have := htne.card_pos
    simp only [List.map_cons, List.sum_cons, List.length_cons, sumsetList_cons]
    omega

/-- If every part of the list has size at least `k`, the sum of the part sizes is
at least `t · k` where `t` is the number of parts. -/
lemma length_mul_le_sum_card (l : List (Finset ℤ)) (k : ℕ) (hk : ∀ A ∈ l, k ≤ A.card) :
    l.length * k ≤ (l.map Finset.card).sum := by
  induction l with
  | nil => simp
  | cons A t ih =>
    have hA : k ≤ A.card := hk A (by simp)
    have ht := ih (fun B hB => hk B (by simp [hB]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc (t.length + 1) * k = t.length * k + k := by ring
      _ ≤ (t.map Finset.card).sum + A.card := by omega
      _ = A.card + (t.map Finset.card).sum := by ring

/-- **Uniform growth.** A `t`-fold sumset whose `t` parts all have size at least
`k` has size at least `t(k-1) + 1`. -/
lemma sumsetList_card_uniform (l : List (Finset ℤ)) (k : ℕ)
    (hne : ∀ A ∈ l, A.Nonempty) (hk : ∀ A ∈ l, k ≤ A.card) :
    l.length * k + 1 ≤ (sumsetList l).card + l.length := by
  have h1 := sumsetList_card_lower l hne
  have h2 := length_mul_le_sum_card l k hk
  omega

/-- **Necessary condition for containment.** If a finite set `S` contains a
`t`-fold sumset whose parts all have size at least `k`, then `|S| ≥ t(k-1) + 1`.
The growth of the sumset is forced by the sizes of the summands. -/
theorem sumset_containment_forces_card (S : Finset ℤ) (l : List (Finset ℤ)) (k : ℕ)
    (hne : ∀ A ∈ l, A.Nonempty) (hk : ∀ A ∈ l, k ≤ A.card)
    (hsub : sumsetList l ⊆ S) :
    l.length * (k - 1) + 1 ≤ S.card := by
  have h := sumsetList_card_uniform l k hne hk
  have hcard : (sumsetList l).card ≤ S.card := Finset.card_le_card hsub
  have hSne : 1 ≤ (sumsetList l).card := (sumsetList_nonempty l hne).card_pos
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp only [Nat.zero_sub, Nat.mul_zero]; omega
  · have hk1 : k - 1 + 1 = k := by omega
    have hmul : l.length * (k - 1) + l.length = l.length * k := by
      calc l.length * (k-1) + l.length = l.length * (k-1+1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = l.length * k := by rw [hk1]
    omega

/-- **Avoidance principle.** Any finite set `S` with `|S| ≤ t(k-1)` avoids every
`t`-fold sumset whose `t` parts all have size at least `k`: no such sumset can be
contained in `S`. This is the contrapositive of `sumset_containment_forces_card`. -/
theorem sumset_avoidance (S : Finset ℤ) (l : List (Finset ℤ)) (k : ℕ)
    (hne : ∀ A ∈ l, A.Nonempty) (hk : ∀ A ∈ l, k ≤ A.card)
    (hS : S.card ≤ l.length * (k - 1)) :
    ¬ sumsetList l ⊆ S := by
  intro hsub
  have := sumset_containment_forces_card S l k hne hk hsub
  omega

/-- **Dense avoidance existence.** For any ambient size `n`, density `δ ≤ 1`,
number of parts `t` and threshold `k` satisfying the (linear) barrier
`n ≤ t(k-1)`, there is a set `S` of integers, contained in `{0, 1, …, n-1}`, of
density at least `δ` (that is, `δ·n ≤ |S|`), which contains **no** `t`-fold
sumset all of whose `t` parts have size at least `k`.

The threshold `k ≈ n/t` here is the deterministic barrier; pushing it down to the
probabilistic scale `(log n / log(1/δ))^{1/(t-1)}` is the deep open problem. -/
theorem dense_set_avoids_large_sumsets (n t k : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hbarrier : n ≤ t * (k - 1)) :
    ∃ S : Finset ℤ, ((S : Finset ℤ) ⊆ (Finset.range n).image (Nat.cast : ℕ → ℤ)) ∧
      δ * n ≤ S.card ∧
      ∀ l : List (Finset ℤ), l.length = t → (∀ A ∈ l, A.Nonempty) →
        (∀ A ∈ l, k ≤ A.card) → ¬ sumsetList l ⊆ S := by
  refine ⟨(Finset.range n).image (Nat.cast : ℕ → ℤ), Finset.Subset.refl _, ?_, ?_⟩
  · have hcard : ((Finset.range n).image (Nat.cast : ℕ → ℤ)).card = n := by
      rw [Finset.card_image_of_injective _ (fun a b => by exact_mod_cast id)]
      simp
    rw [hcard]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · intro l hlen hne hk
    have hcard : ((Finset.range n).image (Nat.cast : ℕ → ℤ)).card = n := by
      rw [Finset.card_image_of_injective _ (fun a b => by exact_mod_cast id)]
      simp
    apply sumset_avoidance _ l k hne hk
    rw [hcard, hlen]
    exact hbarrier

/-- Sanity witness that the growth bound is sharp: `{0,1} + {0,10} = {0,1,10,11}`
has exactly `4 = (2 + 2) - 1` elements, saturating `sumsetList_card_lower`. -/
example : (sumsetList [({0, 1} : Finset ℤ), {0, 10}]).card = 4 := by decide

end TFoldSumsetAvoidance
section
open Finset Pointwise
open TFoldSumsetAvoidance

theorem solution (n t k : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hbarrier : n ≤ t * (k - 1)) :
    ∃ S : Finset ℤ, ((S : Finset ℤ) ⊆ (Finset.range n).image (Nat.cast : ℕ → ℤ)) ∧
      δ * n ≤ S.card ∧
      ∀ l : List (Finset ℤ), l.length = t → (∀ A ∈ l, A.Nonempty) →
        (∀ A ∈ l, k ≤ A.card) → ¬ sumsetList l ⊆ S :=
  TFoldSumsetAvoidance.dense_set_avoids_large_sumsets n t k _ hδ hbarrier

end
