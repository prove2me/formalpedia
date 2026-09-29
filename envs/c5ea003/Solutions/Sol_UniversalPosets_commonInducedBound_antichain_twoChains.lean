-- Prove2me | solution 1 for UniversalPosets.commonInducedBound_antichain_twoChains
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:24:57.213416+00:00
-- url     : https://prove2.me/submissions/15733ed7-80af-4cf6-9673-fadb73cb3e3b

-- Sol generated from Cryptography/UniversalPosets/ThreePosetBound.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound

/-!
# A three-poset overlap bound: `U(n) ≥ 3n - ⌈n/2⌉ - 3`

`ExactSmall.lean` proved `2n - 1 ≤ U(n)` by playing the `n`-chain against the
`n`-antichain: two induced copies of posets with no large common induced
subposet cannot overlap much inside a host.  Here the method is pushed to a
*third* poset, the disjoint union of two chains of lengths `⌈n/2⌉` and `⌊n/2⌋`
(`twoChains`), whose common induced subposets with the chain and with the
antichain have at most `⌈n/2⌉` and `2` points respectively.  Bonferroni's
inequality for three sets then gives

`3n - (1 + ⌈n/2⌉ + 2) ≤ U(n)`,

i.e. asymptotically `U(n) ≥ 5n/2 - 3`, which improves `2n - 1` from `n = 6` on
(and agrees with it for `n ≤ 5`, where the earlier bound is already sharp for
`n ≤ 3`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The overlap method is not limited to two posets: any
family `P₁,…,P_k` gives `U(n) ≥ kn - Σ_{i<j} s_{ij}` where `s_{ij}` bounds the
common induced subposets.  The optimisation is a genuine extremal problem; the
first nontrivial instance is `k = 3` with chain, antichain, and two chains.

Experiment (Experimenter).  Numerically, `3n - ⌈n/2⌉ - 3` beats `2n - 1` exactly
for `n ≥ 6` (`n = 6`: `12` versus `11`; `n = 10`: `22` versus `19`); both are
dwarfed by the counting bound `2^{(n-1)/4}` from about `n = 24` on.  Adding a
fourth poset was tested on paper and does *not* help: any fourth `n`-element
poset has a chain or an antichain of size at least `√n`, and its overlaps with
the three posets above already exceed the `n` points it contributes.

Analysis (Analyst).  The method is intrinsically linear: `k` posets contribute
`kn` but a fixed pair contributes an overlap at least `Ω(log n)` by
Dilworth/Erdős–Szekeres, and for large `k` the sum of overlaps dominates.  So no
choice of family can push the overlap method past `O(n log n)`; the exponential
lower bound must come from counting, as it does in `LogBounds.lean`.

Critique (Critic).  The bound is stated with truncated natural subtraction, so it
is vacuously weak for very small `n` and no hypothesis `n ≥ 6` is needed; the
sharper claim (that it *improves* on `2n-1`) is a numerical remark, not a
theorem, and is left to the table above.
-/

open UniversalPosets

open Function

/-! ## Bonferroni for three finsets -/


/-! ## The third poset: two disjoint chains -/



/-- Two points on the same side of `twoChains` are comparable. -/
theorem twoChains_comparable_of_same_side {n : ℕ} (x y : Fin n)
    (hside : ((x : ℕ) < (n + 1) / 2) ↔ ((y : ℕ) < (n + 1) / 2)) :
    twoChains n x y ∨ twoChains n y x := by
  rcases le_total x y with h | h
  · exact Or.inl ⟨h, hside⟩
  · exact Or.inr ⟨h, hside.symm⟩



/-! ## The two new overlap bounds -/



/-! ## The three-poset lower bound -/





open UniversalPosets in
theorem solution(n : ℕ) :
    CommonInducedBound (fun x y : Fin n => x = y) (twoChains n) 2 := by
  classical
  intro A φ hinj hiso
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcon
  -- distinct points of `A` land on different sides
  have hdiff : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ (((φ x : ℕ) < (n + 1) / 2) ↔ ((φ y : ℕ) < (n + 1) / 2)) := by
    intro x hx y hy hxy hside
    rcases twoChains_comparable_of_same_side (φ x) (φ y) hside with h | h
    · exact hxy ((hiso x hx y hy).2 h)
    · exact hxy ((hiso y hy x hx).2 h).symm
  have h1 := hdiff a ha b hb hab
  have h2 := hdiff a ha c hc hac
  have h3 := hdiff b hb c hc hbc
  tauto
