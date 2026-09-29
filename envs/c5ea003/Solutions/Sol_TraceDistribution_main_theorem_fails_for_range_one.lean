-- Prove2me | solution 1 for TraceDistribution.main_theorem_fails_for_range_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:36:28.895366+00:00
-- url     : https://prove2.me/submissions/25a38651-1b15-44ac-ba7f-92821a282cbb

-- Sol generated from Logic/TraceDistribution/Examples.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core
import Theorems.Thm_TraceDistribution_card_orbits_eq_of_traceDistribution_eq
import Theorems.Thm_TraceDistribution_fixedCard_regular
import Theorems.Thm_TraceDistribution_orbitCount_mul_card_group
import Theorems.Thm_TraceDistribution_powerSum_traceDistribution
/-
# The threshold in Conjecture A is not an artefact: low-degree data is genuinely blind

`Logic.TraceDistribution.Core` proves that the trace distribution of a finite
`G`-action is determined by the orbit counts on `k`-tuples for `k ≤ max |X| |Y|`.
It is natural to ask whether the plain orbit count (`k = 1`, i.e. Burnside's lemma
itself) already suffices.  It does not, and the failure is universal:

For **every** finite group `G` with `|G| ≥ 2`, the *regular* `G`-set `G` and the
*one-point* `G`-set `Unit` have

* the same number of orbits on `0`-tuples (both `1`),
* the same number of orbits on `1`-tuples (both `1`),
* but different numbers of orbits on `2`-tuples (`|G|` versus `1`),

and consequently different trace distributions (`{|G|, 0, …, 0}` versus
`{1, 1, …, 1}`).  See `regular_ne_point`.

Taking `G` of order `2` makes this optimal on the nose: there `max |X| |Y| = 2`, so
the range `k ≤ 2` supplied by the main theorem is exactly the range needed.

## Lab notes (experimental data)

`G = ℤ/2`:

| action        | trace distribution | `k=0` | `k=1` | `k=2` | `k=3` |
|---------------|--------------------|-------|-------|-------|-------|
| regular `G`   | `{2, 0}`           | 1     | 1     | 2     | 4     |
| point `Unit` | `{1, 1}`           | 1     | 1     | 1     | 1     |

`G = ℤ/3`: regular `{3,0,0}` gives `1, 1, 3, 9, …`; point `{1,1,1}` gives `1, 1, 1, …`.
In general `|orbits on G^k| = |G|^{k-1}` for the regular action and `1` for the point.
-/

open MulAction Finset

open TraceDistribution

variable {G : Type*} [Group G] [Fintype G]

/-! ## Fixed-point counts of the two extreme `G`-sets -/


omit [Fintype G] in
theorem fixedCard_unit (g : G) : fixedCard Unit g = 1 := by
  have huniv : fixedBy Unit g = Set.univ := by
    ext x
    simp [mem_fixedBy, Subsingleton.elim (g • x) x]
  rw [fixedCard, huniv]
  simp

/-! ## Power sums of the two extreme `G`-sets -/

theorem powerSum_regular_succ [DecidableEq G] (k : ℕ) :
    (Multiset.map (fun a => a ^ (k + 1)) (traceDistribution G G)).sum = (Nat.card G) ^ (k + 1) := by
  rw [powerSum_traceDistribution]
  have hterm : ∀ g : G, (fixedCard G g) ^ (k + 1)
      = if g = 1 then (Nat.card G) ^ (k + 1) else 0 := by
    intro g
    rw [fixedCard_regular]
    split
    · rfl
    · exact zero_pow (Nat.succ_ne_zero k)
  rw [Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_ite_eq' Finset.univ (1 : G)]
  simp

theorem powerSum_unit (k : ℕ) :
    (Multiset.map (fun a => a ^ k) (traceDistribution G Unit)).sum = Nat.card G := by
  rw [powerSum_traceDistribution]
  simp [fixedCard_unit, Nat.card_eq_fintype_card]

/-! ## Orbit counts of the two extreme `G`-sets -/

/-- The one-point `G`-set has exactly one orbit on `k`-tuples, for every `k`. -/
theorem orbitCount_unit (k : ℕ) : orbitCount G Unit k = 1 := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have h := orbitCount_mul_card_group G Unit k
  rw [powerSum_unit] at h
  have h1 : orbitCount G Unit k * Nat.card G = 1 * Nat.card G := by rw [h, one_mul]
  exact Nat.eq_of_mul_eq_mul_right hG h1

/-- The regular `G`-set has `|G|^{k}` orbits on `(k+1)`-tuples. -/
theorem orbitCount_regular_succ [DecidableEq G] (k : ℕ) :
    orbitCount G G (k + 1) = (Nat.card G) ^ k := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have h := orbitCount_mul_card_group G G (k + 1)
  rw [powerSum_regular_succ] at h
  have h1 : orbitCount G G (k + 1) * Nat.card G = (Nat.card G) ^ k * Nat.card G := by
    rw [h, pow_succ]
  exact Nat.eq_of_mul_eq_mul_right hG h1

theorem orbitCount_regular_zero : orbitCount G G 0 = 1 := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have h := orbitCount_mul_card_group G G 0
  have hsum : (Multiset.map (fun a => a ^ 0) (traceDistribution G G)).sum = Nat.card G := by
    rw [powerSum_traceDistribution]
    simp [Nat.card_eq_fintype_card]
  rw [hsum] at h
  have h1 : orbitCount G G 0 * Nat.card G = 1 * Nat.card G := by rw [h, one_mul]
  exact Nat.eq_of_mul_eq_mul_right hG h1

/-! ## The separation -/

/-- **Burnside's lemma alone is blind.**  For any finite group of order at least `2`,
the regular `G`-set and the one-point `G`-set agree on `0`- and `1`-tuples but not on
`2`-tuples; hence no version of the main theorem with the range `k ≤ 1` can hold. -/
theorem regular_vs_point_separation [DecidableEq G] (h2 : 2 ≤ Nat.card G) :
    orbitCount G G 0 = orbitCount G Unit 0 ∧
    orbitCount G G 1 = orbitCount G Unit 1 ∧
    orbitCount G G 2 ≠ orbitCount G Unit 2 := by
  refine ⟨by rw [orbitCount_regular_zero, orbitCount_unit], ?_, ?_⟩
  · rw [orbitCount_unit]
    simpa using orbitCount_regular_succ (G := G) 0
  · rw [orbitCount_unit]
    have : orbitCount G G 2 = Nat.card G := by
      simpa using orbitCount_regular_succ (G := G) 1
    omega

/-- The two `G`-sets really do have different trace distributions. -/
theorem regular_ne_point [DecidableEq G] (h2 : 2 ≤ Nat.card G) :
    traceDistribution G G ≠ traceDistribution G Unit := by
  intro h
  obtain ⟨-, -, hne⟩ := regular_vs_point_separation (G := G) h2
  exact hne (card_orbits_eq_of_traceDistribution_eq G Unit h 2)



open TraceDistribution in
theorem solution:
    ¬ (∀ (G : Type) [Group G] [Fintype G] (X Y : Type)
        [MulAction G X] [MulAction G Y] [Finite X] [Finite Y],
        (∀ k ≤ 1, orbitCount G X k = orbitCount G Y k) →
          traceDistribution G X = traceDistribution G Y) := by
  intro hcontra
  classical
  have h2 : 2 ≤ Nat.card (Multiplicative (ZMod 2)) := by
    simp [Nat.card_eq_fintype_card]
  obtain ⟨h0, h1, -⟩ := regular_vs_point_separation (G := Multiplicative (ZMod 2)) h2
  refine regular_ne_point (G := Multiplicative (ZMod 2)) h2 ?_
  refine hcontra (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)) Unit ?_
  intro k hk
  interval_cases k
  · exact h0
  · exact h1
