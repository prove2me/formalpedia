-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.labelSeq_deletionParity_of_not_injective_of_noOpposite
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:20.569772+00:00
-- url     : https://prove2.me/submissions/4eca6c61-2446-4908-9a68-4f5ec921e07b

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

















theorem alternatingNegLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    (alternatingLabelOf idx a).neg = (alternatingLabelOf idx b).neg ↔ a = b := by
  constructor
  · intro h
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  · intro h
    subst h
    rfl

theorem alternatingNegLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingNegLabelSetOf idx).card = r := by
  classical
  rw [alternatingNegLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingNegLabelOf_inj hidx).mp h























/-! ### Pure sign-sequence deletion parity -/









































/-! ### Sorted label-sequence deletion parity -/

























































/-! ## Ky Fan parity statement on the non-degenerate range -/



































theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra t : Fin (r + 1)} {k : Fin r}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply (alternatingLabelOf_inj hidx).mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetOf idx ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetOf] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetOf idx).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = r := by
      simp [retained]
    simpa [alternatingLabelSetOf_card hidx, hretained] using himage_le
  have hEq : alternatingLabelSetOf idx = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_injOn {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
    (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetOf_card hidx]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door
      (idx := idx) hidx (extra := extra) (t := t) (k := k)
      hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := (alternatingLabelOf_inj hidx).mp
            (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSetOf] using hdoorExtra
      · simpa [sigmaDoorSetOf] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm





theorem labelSeqSet_delete_eq_erase_image {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
      (Finset.univ.erase j).image L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr
      ⟨j.succAbove a, by simp [Fin.succAbove_ne], ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    rcases Fin.exists_succAbove_eq htne with ⟨a, ha⟩
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, by simpa [← ha] using htlabel⟩

theorem SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {j : Fin (r + 1)} :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      alternatingLabelSetOf idx ⊆ (Finset.univ.erase j).image sigmaLabel := by
  classical
  constructor
  · intro hdoor x hx
    rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr
      ⟨t, by simp [htne], htlabel.trans ha⟩
  · intro hsub a
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
      simp [alternatingLabelSetOf]
    have himage := hsub hmem
    rcases Finset.mem_image.mp himage with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    exact ⟨t, htne, htlabel⟩

theorem IsAltPosLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltPosLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltNegLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltNegLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingNegLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {L : Fin (k + 1) → SignedLabel m}
    (horig : labelSeqSet L = alternatingLabelSetOf idx)
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔
      SigmaDeletionHasAlternatingLabelSetOf idx L j := by
  classical
  constructor
  · intro hdel
    rcases hdel with ⟨eta, heta, hdelSet⟩
    let retained : Finset (Fin (k + 1)) := Finset.univ.erase j
    have hret_eq_del :
        labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
          retained.image L := by
      simpa [retained] using labelSeqSet_delete_eq_erase_image L j
    have hret_subset :
        retained.image L ⊆ alternatingLabelSetOf idx := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
      have hxorig : x ∈ labelSeqSet L := by
        rw [← htlabel]
        simp [labelSeqSet]
      simpa [horig] using hxorig
    have hret_card : (retained.image L).card = k := by
      rw [← hret_eq_del, hdelSet, alternatingLabelSetOf_card heta.injective]
    have halt_card : (alternatingLabelSetOf idx).card = k :=
      alternatingLabelSetOf_card hidx.injective
    have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
      apply Finset.eq_of_subset_of_card_le hret_subset
      rw [hret_card, halt_card]
    exact SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image.mpr
      (by simpa [retained, hret_eq_alt])
  · intro hdoor
    refine ⟨idx, hidx, ?_⟩
    have himage :=
      sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
        (idx := idx) hidx.injective (sigmaLabel := L) (extra := j) hdoor
    rw [labelSeqSet_delete_eq_erase_image, himage]























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

theorem solution {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hnot : ¬ Function.Injective L)
    (_hno : NoOppositeLabelSeq L) :
    Even (labelSeqAltPosDeletionSet L).card ∧
      ¬ IsAltPosLabelSeq L ∧ ¬ IsAltNegLabelSeq L := by
  classical
  have hnotAltPos : ¬ IsAltPosLabelSeq L := by
    intro h
    exact hnot h.injective
  have hnotAltNeg : ¬ IsAltNegLabelSeq L := by
    intro h
    exact hnot h.injective
  have heven : Even (labelSeqAltPosDeletionSet L).card := by
    by_cases hnonempty : (labelSeqAltPosDeletionSet L).Nonempty
    · rcases hnonempty with ⟨j0, hj0⟩
      have hdel0 :
          IsAltPosLabelSeq (fun a : Fin k => L (j0.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj0
      rcases hdel0 with ⟨idx, hidx, hdelSet⟩
      let retained : Finset (Fin (k + 1)) := Finset.univ.erase j0
      have hret_eq_del :
          labelSeqSet (fun a : Fin k => L (j0.succAbove a)) =
            retained.image L := by
        simpa [retained] using labelSeqSet_delete_eq_erase_image L j0
      have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
        rw [← hret_eq_del, hdelSet]
      have hret_subset_orig : retained.image L ⊆ labelSeqSet L := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
        rw [← htlabel]
        simp [labelSeqSet]
      have hcard_orig_le : (labelSeqSet L).card ≤ k := by
        have himage_le :
            (labelSeqSet L).card ≤ k + 1 := by
          simpa [labelSeqSet] using
            (Finset.card_image_le :
              (Finset.univ.image L).card ≤
                (Finset.univ : Finset (Fin (k + 1))).card)
        have hneq : (labelSeqSet L).card ≠ k + 1 := by
          intro hcard
          have hcard_image :
              (Finset.univ.image L).card =
                (Finset.univ : Finset (Fin (k + 1))).card := by
            simpa [labelSeqSet] using hcard
          have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin (k + 1))) :=
            (Finset.card_image_iff).mp hcard_image
          exact hnot (by
            intro a b hab
            exact hinjOn (by simp) (by simp) hab)
        omega
      have hcard_ret : (retained.image L).card = k := by
        rw [hret_eq_alt, alternatingLabelSetOf_card hidx.injective]
      have hcard_orig_ge : k ≤ (labelSeqSet L).card := by
        have hle : (retained.image L).card ≤ (labelSeqSet L).card :=
          Finset.card_le_card hret_subset_orig
        omega
      have hcard_orig : (labelSeqSet L).card = k := by
        omega
      have hret_eq_orig : retained.image L = labelSeqSet L := by
        apply Finset.eq_of_subset_of_card_le hret_subset_orig
        rw [hcard_orig, hcard_ret]
      have horig : labelSeqSet L = alternatingLabelSetOf idx := by
        rw [← hret_eq_orig, hret_eq_alt]
      have hdoor0 : SigmaDeletionHasAlternatingLabelSetOf idx L j0 := by
        exact (IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
          (idx := idx) hidx (L := L) horig j0).mp
          ⟨idx, hidx, hdelSet⟩
      have hextra_mem : L j0 ∈ alternatingLabelSetOf idx := by
        have hmem : L j0 ∈ labelSeqSet L := by
          simp [labelSeqSet]
        simpa [horig] using hmem
      rcases (by simpa [alternatingLabelSetOf] using hextra_mem) with ⟨a, ha⟩
      have hextra : L j0 = alternatingLabelOf idx a := ha.symm
      have hfixedCard :
          (sigmaDoorSetOf idx L).card = 2 :=
        sigmaDoorSetOf_card_duplicate_of_door
          (idx := idx) hidx.injective (sigmaLabel := L) (extra := j0)
          (k := a) hdoor0 hextra
      have hset :
          labelSeqAltPosDeletionSet L = sigmaDoorSetOf idx L := by
        ext j
        simp [labelSeqAltPosDeletionSet, sigmaDoorSetOf,
          IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
            (idx := idx) hidx (L := L) horig j]
      rw [hset, hfixedCard]
      simp
    · have hempty : labelSeqAltPosDeletionSet L = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simp
  exact ⟨heven, hnotAltPos, hnotAltNeg⟩
