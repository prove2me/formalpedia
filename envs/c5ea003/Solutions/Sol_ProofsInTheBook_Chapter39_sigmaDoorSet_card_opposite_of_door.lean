-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.sigmaDoorSet_card_opposite_of_door
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:09:32.824858+00:00
-- url     : https://prove2.me/submissions/6d85c353-ff9c-4858-85e2-9e8dec3c68a4

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







theorem alternatingLabel_inj {d : ℕ} {a b : Fin d} :
    alternatingLabel a = alternatingLabel b ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg SignedLabel.index h
    simpa [alternatingLabel] using hidx
  · intro h
    subst h
    rfl

theorem alternatingLabel_neg_ne {d : ℕ} (a b : Fin d) :
    (alternatingLabel a).neg ≠ alternatingLabel b := by
  intro h
  have hidx : a = b := by
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabel, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabel, SignedLabel.neg] at hpos





theorem alternatingLabelSetA_card (d : ℕ) :
    (alternatingLabelSetA d).card = d := by
  classical
  rw [alternatingLabelSetA, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact alternatingLabel_inj.mp h

/-! ### Alternating labels along an arbitrary increasing index set -/











































/-! ### Pure sign-sequence deletion parity -/









































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













theorem sigmaDeletionHasAlternatingLabelSet_retained_image_eq {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetA d := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetA d ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetA] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetA d).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = d := by
      simp [retained]
    simpa [alternatingLabelSetA_card, hretained] using himage_le
  have hEq : alternatingLabelSetA d = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_injOn {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSet_retained_image_eq
    (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetA_card]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard













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

theorem solution {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact alternatingLabel_neg_ne k b (hextra.symm.trans hulabel)
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSet] using hdoorExtra
  rw [hset]
  simp
