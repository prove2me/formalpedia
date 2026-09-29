-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesSharpPair
-- name    : Combinatorics_QuartetCodesSharpPair
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:08.932887+00:00
-- url     : https://prove2.me/theorems/289f158d-582d-42d2-b33a-32b41b1113b9
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesSharpPair
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesSharpPair`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesSharpPair.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes

/-!
# The two-tree quartet threshold is exactly six leaves

`Combinatorics.QuartetCodesUpperBound` shows by Erdős–Szekeres that any two caterpillars on ten
leaves share a quartet, while `QuartetCodes.not_isAgreementThreshold_five_two` exhibits two
caterpillars on five leaves sharing none.  Here the upper end is pushed down to the truth: **six**
leaves already force a common quartet, so the two-tree threshold is exactly `6`.

The proof is the coding-theoretic restriction principle in action.  A quartet letter depends only on
the *relative order* of the four leaves, so restricting a leaf order to any six leaves produces a
genuine six-leaf codeword (`qcode_restrict`), and a six-leaf statement transfers to every larger
leaf set.  The six-leaf statement itself is reduced by the group action
`(π, ρ) ↦ (1, ρ π⁻¹)` to a single quantifier over `Sym(6)` and then decided by the kernel.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Exhaustive computation says that all `720²` pairs of six-leaf caterpillars share a quartet, i.e.
`h(2) = 6`; the Erdős–Szekeres value `10` is an artefact of the proof method.

## Experiment (Experimenter)
Deciding `∀ π ρ : Sym(6), ∃ quartet` directly is `518400` pairs and is out of kernel reach.  Using
the right translation action of `Sym(6)` on pairs, the statement collapses to `720` cases
(`six_leaf_core`), which the kernel checks in about two minutes.  The transfer to `n ≥ 6` leaves
needs the rank permutation of an injective map (`rankPerm`) and the order-invariance of the ternary
letter (`code3_congr`).

## Analysis (Analyst)
The gain (from `10` down to `6`) comes entirely from *not* using Erdős–Szekeres: the quartet letter
is an order invariant, so a purely local six-leaf obstruction suffices.  The same mechanism should
sharpen the `k`-tree bound `3^{2^k}` if the corresponding finite statement can be decided for the
relevant window size.

## Critique (Critic)
`code3_congr` is stated with all twelve order comparisons, so it does not silently assume the four
leaves are distinct; `rankPerm` is built from an explicit rank function with a proved injectivity,
so the statement uses no choice beyond what `Equiv.ofBijective` needs.  The final theorem quantifies
over *all* pairs of leaf orders on *all* `n ≥ 6`, and the exhibited quartet is genuinely made of
four distinct leaves.
-/

open Finset

namespace QuartetCodes

section Restriction

variable {m n : ℕ}


/-- The rank of `i` among the values of `g`. -/
def rankOf (g : Fin m → Fin n) (i : Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun j => (g j).val < (g i).val)).card

lemma rankOf_lt (g : Fin m → Fin n) (i : Fin m) : rankOf g i < m := by
  unfold rankOf
  have hsub : ((Finset.univ : Finset (Fin m)).filter (fun j => (g j).val < (g i).val))
      ⊆ (Finset.univ : Finset (Fin m)).erase i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact absurd hj.2 (lt_irrefl _)
  have hcard := Finset.card_le_card hsub
  have : ((Finset.univ : Finset (Fin m)).erase i).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hm : 0 < m := i.pos
  omega

lemma rankOf_lt_of_lt {g : Fin m → Fin n} {i j : Fin m} (h : (g i).val < (g j).val) :
    rankOf g i < rankOf g j := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩
  · intro hsub
    have hi : i ∈ (Finset.univ : Finset (Fin m)).filter (fun x => (g x).val < (g j).val) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    have := hsub hi
    rw [Finset.mem_filter] at this
    exact absurd this.2 (lt_irrefl _)


/-- The permutation of `Fin m` recording the ranks of an injective map `g : Fin m → Fin n`. -/
noncomputable def rankPerm (g : Fin m → Fin n) (hg : Function.Injective g) :
    Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun i => (⟨rankOf g i, rankOf_lt g i⟩ : Fin m))
    (Finite.injective_iff_bijective.1 (by
      intro i j hij
      have h : rankOf g i = rankOf g j := congrArg Fin.val hij
      rcases lt_trichotomy (g i).val (g j).val with hlt | heq | hgt
      · exact absurd (rankOf_lt_of_lt hlt) (by omega)
      · exact hg (Fin.val_injective heq)
      · exact absurd (rankOf_lt_of_lt hgt) (by omega)))



end Restriction

section SixLeaves





end SixLeaves

end QuartetCodes


