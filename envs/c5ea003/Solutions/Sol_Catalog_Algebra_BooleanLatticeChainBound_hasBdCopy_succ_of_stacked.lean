-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.hasBdCopy_succ_of_stacked
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:50:51.321293+00:00
-- url     : https://prove2.me/submissions/2a1c20ea-0855-4976-85bc-44560d0555b3

-- Sol generated from Algebra/BooleanLatticeChainBound.lean
import Mathlib
import Definitions.Def_Algebra_BooleanLatticeChainBound
/-
# Forbidden Boolean-lattice subposets: the chain bound and its sharpening

This file develops, from scratch, a formal framework for the extremal problem

  `La(n, B_d) = max { |F| : F ⊆ 2^[n], F contains no (weak) copy of the Boolean lattice B_d }`

and proves the classical *chain bound* `La(n, B_d) ≤ (2^d - 1) * C(n, ⌊n/2⌋)`
together with a number of complementary results relevant to the conjecture
`La(n, B_d) ≤ (d + c) * C(n, ⌊n/2⌋)` for an absolute constant `c`.

## Main definitions

* `HasBdCopy d F` : the family `F` of subsets of `Fin n` contains a *weak* copy of the
  `d`-dimensional Boolean lattice, i.e. an injective, containment-preserving map
  `Finset (Fin d) → F`.
* `BdFree d F`    : `F` contains no such copy.
* `HasChain k F`  : `F` contains a strictly increasing chain of `k` sets.
* `La n d`        : the extremal function, the supremum of `|F|` over `B_d`-free `F`.

## Main results

* `hasBdCopy_of_hasChain`    : a chain of `2^d` sets already yields a weak copy of `B_d`.
* `lubell_le_of_no_chain`    : the Lubell mass of a `(k+1)`-chain-free family is at most `k`
  (a Mirsky-type induction feeding into the LYM inequality). This is strictly stronger
  than the corresponding cardinality bound.
* `card_le_of_bdFree`        : the chain bound `|F| ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_le_chain_bound`        : `La n d ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_one`                   : `La n 1 = C(n, ⌊n/2⌋)` (Sperner's theorem, both directions).
* `La_le_height_bound`       : `La n d ≤ (n+1) * C(n, ⌊n/2⌋)`, hence the conjectured bound
  `(d + 1) * C(n, ⌊n/2⌋)` holds unconditionally whenever `n ≤ d`.
* `La_three_le_four_of_le_eight` : the conjectured `d = 3` bound `La n 3 ≤ 4 * C(n, ⌊n/2⌋)`
  holds for every `n ≤ 8`.
* `La_ge_consecutive_levels` : the lower bound coming from `d` consecutive levels,
  `La n d ≥ ∑_{i=a}^{a+d-1} C(n, i)`.
* `hasBdCopy_succ_of_stacked` and `hasBdCopy_succ_of_parallel_chains` : a *doubling*
  criterion showing that a `B_{d+1}` copy already arises from two "parallel" `B_d` copies,
  a configuration strictly weaker than a single long chain.
-/


open Catalog.Algebra.BooleanLatticeChainBound

open Finset

/-! ## The central binomial coefficient -/




/-! ## Weak copies of the Boolean lattice -/

variable {n : ℕ}





/-! ## A linear extension of `B d` -/






/-! ## Chains produce Boolean-lattice copies -/




/-! ## Mirsky + LYM : the Lubell mass of a chain-free family -/







  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/












/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/









/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/


lemma restr_mono {d : ℕ} {U V : Finset (Fin (d + 1))} (h : U ⊆ V) : restr U ⊆ restr V := by
  intro i hi
  simp only [restr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h hi

lemma restr_ext {d : ℕ} {U V : Finset (Fin (d + 1))} (hr : restr U = restr V)
    (hl : (Fin.last d ∈ U) ↔ (Fin.last d ∈ V)) : U = V := by
  ext i
  induction i using Fin.lastCases with
  | last => exact hl
  | cast j =>
    have h1 : j ∈ restr U ↔ j ∈ restr V := by rw [hr]
    simpa [restr] using h1





open Catalog.Algebra.BooleanLatticeChainBound in
theorem solution{d : ℕ} {F : Finset (Finset (Fin n))}
    (f h : Finset (Fin d) → Finset (Fin n))
    (hfinj : Function.Injective f) (hhinj : Function.Injective h)
    (hfF : ∀ S, f S ∈ F) (hhF : ∀ S, h S ∈ F)
    (hfmono : ∀ S T, S ⊆ T → f S ⊆ f T) (hhmono : ∀ S T, S ⊆ T → h S ⊆ h T)
    (hstack : ∀ S, f S ⊆ h S) (hne : ∀ S T, f S ≠ h T) :
    HasBdCopy (d + 1) F := by
  classical
  refine ⟨fun U => if Fin.last d ∈ U then h (restr U) else f (restr U), ?_, ?_, ?_⟩
  · intro U V hUV
    by_cases hU : Fin.last d ∈ U <;> by_cases hV : Fin.last d ∈ V <;>
      simp only [hU, hV, if_true, if_false] at hUV
    · exact restr_ext (hhinj hUV) (by simp [hU, hV])
    · exact absurd hUV.symm (hne _ _)
    · exact absurd hUV (hne _ _)
    · exact restr_ext (hfinj hUV) (by simp [hU, hV])
  · intro U
    by_cases hU : Fin.last d ∈ U <;> simp [hU, hfF, hhF]
  · intro U V hUV
    have hr : restr U ⊆ restr V := restr_mono hUV
    by_cases hU : Fin.last d ∈ U <;> by_cases hV : Fin.last d ∈ V <;>
      simp only [hU, hV, if_true, if_false]
    · exact hhmono _ _ hr
    · exact absurd (hUV hU) hV
    · exact (hfmono _ _ hr).trans (hstack _)
    · exact hfmono _ _ hr
