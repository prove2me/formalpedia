-- Prove2me | solution 1 for QuartetCodes.caterpillar_pair_common_quartet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:50:39.68856+00:00
-- url     : https://prove2.me/submissions/dff5d584-1384-4c7c-a454-161f2c13e396

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_code3_eq_zero_iff
import Theorems.Thm_QuartetCodes_exists_monotone_chain

/-!
# A matching upper bound: two caterpillars on ten leaves always share a quartet

The companion file `Combinatorics.QuartetCodes` produces, by a first-moment count in ternary
quartet-signature space, exponentially many caterpillar trees with *no* common quartet.  This file
proves the opposite kind of statement for two trees, and is therefore the boundary of the
lower-bound method: **any two caterpillars on at least ten leaves display a common quartet**.

The engine is a self-contained proof of the Erdős–Szekeres theorem in the shape we need: an
injective map on a linearly ordered fintype with more than `9` elements has a strictly monotone
(increasing or decreasing) subset of size four.  Combined with the observation that a quadruple of
leaves ordered the same way — or in exactly opposite ways — by two caterpillars carries the same
quartet type, this yields the upper bound.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Since the first-moment bound needs `n^4 < 3^m`, it is vacuous for two trees (`m = 1`).  Conjecture:
for two trees a *constant* number of leaves already forces a common quartet, and Erdős–Szekeres
supplies the constant.

## Experiment (Experimenter)
Exhaustive search over all `120^2` pairs of leaf orders on five leaves found pairs with no common
quartet; over all pairs on six leaves none exists (see `ComputationalEvidence.md`).  So the true
threshold for two caterpillars is `6`; Erdős–Szekeres with `r = s = 3` proves `10`, and the
five-leaf pair `not_isAgreementThreshold_five_two` shows the truth is at least `6`.

## Analysis (Analyst)
The gap `6 ≤ h_cat(2) ≤ 10` isolates exactly what the monotone-subsequence argument loses: it
insists on a quadruple that is monotone, whereas a common quartet only needs the *unordered*
`2 + 2` split to coincide.

## Critique (Critic)
The upper bound is proved for caterpillars (leaf orders), the same class in which the lower bound
constructs its avoiding families, so the two bounds are comparable.  Nothing here is proved by
`decide` on the whole statement: the Erdős–Szekeres step is a genuine pigeonhole over the pair
`(longest increasing chain, longest decreasing chain)`.
-/

open Finset

open QuartetCodes

/-! ## Erdős–Szekeres, self-contained -/


variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]
















/-- The special case used below: more than nine elements force a monotone quadruple. -/
theorem exists_monotone_four (f : α → β) (hf : Function.Injective f)
    (hcard : 9 < Fintype.card α) :
    ∃ t : Finset α, 4 ≤ t.card ∧ (IsIncChain f t ∨ IsDecChain f t) := by
  obtain ⟨t, ht, hchain⟩ := exists_monotone_chain f hf (r := 3) (by omega)
  exact ⟨t, by omega, hchain⟩


/-! ## Two caterpillars on ten leaves share a quartet -/


variable {n : ℕ}

/-- Four leaves listed in increasing order of a monotone (or antitone) chain. -/
lemma exists_four_of_card {t : Finset (Fin n)} (ht : 4 ≤ t.card) :
    ∃ x y z w : Fin n, x ∈ t ∧ y ∈ t ∧ z ∈ t ∧ w ∈ t ∧ x < y ∧ y < z ∧ z < w := by
  obtain ⟨t', hsub, hcard⟩ := Finset.exists_subset_card_eq ht
  let e := t'.orderIsoOfFin hcard
  refine ⟨(e 0 : Fin n), (e 1 : Fin n), (e 2 : Fin n), (e 3 : Fin n),
    hsub (e 0).2, hsub (e 1).2, hsub (e 2).2, hsub (e 3).2, ?_, ?_, ?_⟩
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))



/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
theorem solution(hn : 10 ≤ n) (π ρ : Equiv.Perm (Fin n)) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      qcode π a b c d = qcode ρ a b c d := by
  set f : Fin n → Fin n := fun i => ρ (π.symm i) with hf
  have hfinj : Function.Injective f := fun x y hxy => by
    have := π.symm.injective (ρ.injective hxy)
    simpa using this
  have hcard : 9 < Fintype.card (Fin n) := by simpa using (by omega : 9 < n)
  obtain ⟨t, htcard, hchain⟩ := exists_monotone_four f hfinj hcard
  obtain ⟨i, j, k, l, hi, hj, hk, hl, hij, hjk, hkl⟩ := exists_four_of_card htcard
  refine ⟨π.symm i, π.symm j, π.symm k, π.symm l, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt hij)
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt (hij.trans hjk))
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt (hij.trans (hjk.trans hkl)))
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt hjk)
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt (hjk.trans hkl))
  · exact fun h => absurd (π.symm.injective h) (ne_of_lt hkl)
  · have hpi : ∀ x : Fin n, π (π.symm x) = x := fun x => π.apply_symm_apply x
    have hcode_pi : qcode π (π.symm i) (π.symm j) (π.symm k) (π.symm l) = 0 := by
      unfold qcode
      rw [hpi, hpi, hpi, hpi]
      refine (code3_eq_zero_iff _ _ _ _).2 (Or.inl ?_)
      have h1 : i.val < j.val := hij
      have h2 : j.val < k.val := hjk
      have h3 : k.val < l.val := hkl
      omega
    have hcode_rho : qcode ρ (π.symm i) (π.symm j) (π.symm k) (π.symm l) = 0 := by
      have hval : ∀ x : Fin n, ρ (π.symm x) = f x := fun x => rfl
      unfold qcode
      rw [hval, hval, hval, hval]
      refine (code3_eq_zero_iff _ _ _ _).2 ?_
      rcases hchain with hinc | hdec
      · left
        have h1 : (f i).val < (f j).val := hinc i hi j hj hij
        have h2 : (f j).val < (f k).val := hinc j hj k hk hjk
        have h3 : (f k).val < (f l).val := hinc k hk l hl hkl
        omega
      · right
        have h1 : (f j).val < (f i).val := hdec i hi j hj hij
        have h2 : (f k).val < (f j).val := hdec j hj k hk hjk
        have h3 : (f l).val < (f k).val := hdec k hk l hl hkl
        omega
    rw [hcode_pi, hcode_rho]
