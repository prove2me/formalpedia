-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.signSeqDoorSet_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:36.403551+00:00
-- url     : https://prove2.me/submissions/99f747a2-5adf-4e50-af40-21a15215a4d1

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter39 -/
section
set_option autoImplicit true


/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and formalizes Matoušek's finite reduction from a too-small Kneser
coloring to a Tucker-labeling counterexample.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The remaining upstream gap is now the finite Ky Fan boundary-parity count,
formalized in two equivalent ways: `KyFanPrefixParityStatement` says that the
positive-first alternating signed-permutation prefix chains are odd, while
`KyFanPrefixModFourStatement` says that both orientations together have
cardinality `2 mod 4`.  This file proves the Matoušek construction from a
hypothetical `(n - 2*k + 1)`-coloring of `KG(n,k)` to a Tucker counterexample,
proves low-dimensional Tucker cases, packages them into an unconditional
low-dimensional Lovász theorem, proves the one-dimensional Ky Fan prefix-parity
count and the vacuous two-dimensional Ky Fan prefix-parity case, and proves
either Ky Fan parity frontier implies
`TuckerLemmaStatement → chapter39`.
-/

namespace ProofsInTheBook.Chapter39























































/-! ### Tucker-lemma route for the hard lower bound -/



namespace SignedSubset















































end SignedSubset



namespace NonzeroSignedSubset



end NonzeroSignedSubset



namespace SignedLabel





end SignedLabel

































































































namespace SignedPermutation































end SignedPermutation





















































/-! ### Endpoint-count form of the remaining Ky Fan parity frontier -/



















namespace PathEndpointDecomposition



end PathEndpointDecomposition



































































end ProofsInTheBook.Chapter39

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter39
import Mathlib.Data.Fin.Tuple.Sort
-/
/- Source module: ProofsInTheBook.Chapter39Tucker -/
section
set_option autoImplicit true


/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation







/-! ## Hemisphere and equator model -/



























































/-! ## Label-set `A` ridges and the local sigma-degree count -/

















/-! ### Alternating labels along an arbitrary increasing index set -/











































/-! ### Pure sign-sequence deletion parity -/













theorem signSeq_not_bad_iff {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    ¬ signSeqBad s i ↔ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]



theorem signSeqDoor_iff_bad_cut {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    signSeqDoor s i ↔
      (∀ j : Fin (k + 1), j < i → ¬ signSeqBad s j) ∧
        (∀ j : Fin (k + 1), i < j → signSeqBad s j) := by
  constructor
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mpr (h.1 j hji)
    · intro j hij
      exact h.2 j hij
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mp (h.1 j hji)
    · intro j hij
      exact h.2 j hij







theorem signSeqDoor_nonadjacent_false {k : ℕ} {s : Fin (k + 1) → Bool}
    {i j : Fin (k + 1)} (hi : signSeqDoor s i) (hj : signSeqDoor s j)
    (_hij : i < j) :
    j.val ≤ i.val + 1 := by
  by_contra hle
  have hlt : i.val + 1 < j.val := by omega
  let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  have hit : i < t := by
    exact Fin.lt_iff_val_lt_val.mpr (by simp [t])
  have htj : t < j := by
    exact Fin.lt_iff_val_lt_val.mpr (by simpa [t] using hlt)
  have hbad : signSeqBad s t := (signSeqDoor_iff_bad_cut s i).mp hi |>.2 t hit
  have hnot : ¬ signSeqBad s t := (signSeqDoor_iff_bad_cut s j).mp hj |>.1 t htj
  exact hnot hbad















/-! ### Sorted label-sequence deletion parity -/

























































/-! ## Ky Fan parity statement on the non-degenerate range -/















































































/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/











namespace RhoDegreeManifoldData







end RhoDegreeManifoldData





























namespace SignedPermutation















































































end SignedPermutation







































/-! ## Actual upper-hemisphere label-set-`A` graph -/































































/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/





































































/-! ## Actual upper-hemisphere graph with self-contained alternating labels -/





























































/-! ## Antipodal and hemisphere bridges for self-contained alternating chains -/







































































































/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/































end ProofsInTheBook.Chapter39

end


set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem solution {k : ℕ} (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card ≤ 2 := by
  classical
  by_contra hle
  have htwo : 2 < (signSeqDoorSet s).card := by omega
  rcases Finset.two_lt_card.mp htwo with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have hdoor_a : signSeqDoor s a := by simpa [signSeqDoorSet] using ha
  have hdoor_b : signSeqDoor s b := by simpa [signSeqDoorSet] using hb
  have hdoor_c : signSeqDoor s c := by simpa [signSeqDoorSet] using hc
  have hcontr_pair :
      ∀ {x y : Fin (k + 1)}, signSeqDoor s x → signSeqDoor s y → x < y →
        x.val + 1 < y.val → False := by
    intro x y hx hy hxy hgap
    have hle' := signSeqDoor_nonadjacent_false hx hy hxy
    omega
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_trichotomy c a with hca | hcaeq | haclt
    · exact hcontr_pair hdoor_c hdoor_b (lt_trans hca hablt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hca
        have h2 := Fin.lt_iff_val_lt_val.mp hablt
        omega)
    · exact hac hcaeq.symm
    · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
      · exact hcontr_pair hdoor_a hdoor_b hablt (by
          have h1 := Fin.lt_iff_val_lt_val.mp haclt
          have h2 := Fin.lt_iff_val_lt_val.mp hcb
          omega)
      · exact hbc hcbeq.symm
      · exact hcontr_pair hdoor_a hdoor_c (lt_trans hablt hbclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hablt
          have h2 := Fin.lt_iff_val_lt_val.mp hbclt
          omega)
  · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
    · exact hcontr_pair hdoor_c hdoor_a (lt_trans hcb hbalt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hcb
        have h2 := Fin.lt_iff_val_lt_val.mp hbalt
        omega)
    · exact hbc hcbeq.symm
    · rcases lt_trichotomy c a with hca | hcaeq | haclt
      · exact hcontr_pair hdoor_b hdoor_a hbalt (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbclt
          have h2 := Fin.lt_iff_val_lt_val.mp hca
          omega)
      · exact hac hcaeq.symm
      · exact hcontr_pair hdoor_b hdoor_c (lt_trans hbalt haclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbalt
          have h2 := Fin.lt_iff_val_lt_val.mp haclt
          omega)
