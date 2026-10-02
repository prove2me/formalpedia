-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.signSeqDeletionParity
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:34.775142+00:00
-- url     : https://prove2.me/submissions/e8dfe423-1609-49ba-b983-a7b6fa07c7b4

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

theorem signSeq_bad_iff_not_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqBad s i ↔ ¬ s i = decide (Even i.val) := by
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

theorem signSeqDoorSet_card_le_two {k : ℕ} (s : Fin (k + 1) → Bool) :
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

theorem signSeqDoor_next_of_not_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hnot : ¬ signSeqBad s i) (hik : i.val < k) :
    signSeqDoor s ⟨i.val + 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    have hjv : j.val < i.val + 1 := Fin.lt_iff_val_lt_val.mp hj
    by_cases hji : j < i
    · exact hi.1 j hji
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : i.val ≤ j.val := by
          exact le_of_not_gt (by
            intro hv
            exact hji (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hnot
  · intro j hj
    apply hi.2
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : i.val + 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
      omega)

theorem signSeqDoor_prev_of_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hbad : signSeqBad s i) (hi0 : 0 < i.val) :
    signSeqDoor s ⟨i.val - 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    apply hi.1
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : j.val < i.val - 1 := Fin.lt_iff_val_lt_val.mp hj
      omega)
  · intro j hj
    have hjv : i.val - 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
    by_cases hij : i < j
    · exact hi.2 j hij
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : j.val ≤ i.val := by
          exact le_of_not_gt (by
            intro hv
            exact hij (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hbad

theorem signSeqDoorSet_eq_singleton_last_of_altPos {k : ℕ}
    {s : Fin (k + 1) → Bool} (hpos : signSeqAltPos s) :
    signSeqDoorSet s = {Fin.last k} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hilast : i = Fin.last k
    · simp [hilast]
    · have hlt : i < Fin.last k := Fin.lt_last_iff_ne_last.mpr hilast
      have hsuf := hdoor.2 (Fin.last k) hlt
      have hposlast := hpos (Fin.last k)
      have hbad : decide (Even (Fin.last k).val) = !decide (Even (Fin.last k).val) :=
        hposlast.symm.trans hsuf
      cases decide (Even (Fin.last k).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (Fin.last k) := by
      constructor
      · intro j _hj
        exact hpos j
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.le_last j)) hj)
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDoorSet_eq_singleton_zero_of_altNeg {k : ℕ}
    {s : Fin (k + 1) → Bool} (hneg : signSeqAltNeg s) :
    signSeqDoorSet s = {0} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hlt : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have hpref := hdoor.1 0 hlt
      have hneg0 := hneg 0
      have hbad : decide (Even (0 : Fin (k + 1)).val) =
          !decide (Even (0 : Fin (k + 1)).val) :=
        hpref.symm.trans hneg0
      cases decide (Even (0 : Fin (k + 1)).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (0 : Fin (k + 1)) := by
      constructor
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
      · intro j _hj
        exact hneg j
    simpa [signSeqDoorSet] using hdoor





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
    Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s := by
  classical
  constructor
  · intro hodd
    have hle := signSeqDoorSet_card_le_two s
    have hcard : (signSeqDoorSet s).card = 1 := by
      rcases hodd with ⟨a, ha⟩
      omega
    have hposcard : 0 < (signSeqDoorSet s).card := by omega
    obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp hposcard
    have hi : signSeqDoor s i := by simpa [signSeqDoorSet] using hi_mem
    by_cases hk0 : k = 0
    · subst k
      fin_cases i
      by_cases hs0 : s 0 = true
      · left
        intro j
        fin_cases j
        simpa [hs0]
      · right
        have hsfalse : s 0 = false := by
          cases h : s 0 <;> simp [h] at hs0 ⊢
        intro j
        fin_cases j
        simpa [hsfalse]
    · have hend : i = 0 ∨ i = Fin.last k := by
        by_contra hend
        push_neg at hend
        have hi0v : 0 < i.val := Fin.pos_iff_ne_zero.mpr hend.1
        have hikv : i.val < k := by
          have hilast : i ≠ Fin.last k := hend.2
          have hlelast : i ≤ Fin.last k := Fin.le_last i
          have hneval : i.val ≠ k := by
            intro hv
            exact hilast (Fin.ext (by simpa [Fin.last] using hv))
          have hleval : i.val ≤ k := by simpa [Fin.last] using hlelast
          omega
        by_cases hbad : signSeqBad s i
        · let p : Fin (k + 1) := ⟨i.val - 1, by omega⟩
          have hp : signSeqDoor s p := signSeqDoor_prev_of_bad hi hbad hi0v
          have hp_mem : p ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hp
          have hp_ne : p ≠ i := by
            intro hpi
            have hv := congrArg Fin.val hpi
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hp_mem, i, hi_mem, hp_ne⟩
          omega
        · let q : Fin (k + 1) := ⟨i.val + 1, by omega⟩
          have hq : signSeqDoor s q := signSeqDoor_next_of_not_bad hi hbad hikv
          have hq_mem : q ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hq
          have hq_ne : q ≠ i := by
            intro hqi
            have hv := congrArg Fin.val hqi
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hq_mem, i, hi_mem, hq_ne⟩
          omega
      rcases hend with hi0 | hilast
      · right
        intro j
        subst i
        by_cases hj0 : j = 0
        · subst j
          by_contra hnot
          let q : Fin (k + 1) := ⟨1, by omega⟩
          have hnext : signSeqDoor s q := by
            have hkpos : 0 < k := by omega
            have hzero : (0 : Fin (k + 1)).val < k := by simpa using hkpos
            exact signSeqDoor_next_of_not_bad hi
              (by
                intro hb
                exact hnot hb) hzero
          have hnext_mem : q ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hnext
          have hne : q ≠ 0 := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hnext_mem, 0, hi_mem, hne⟩
          omega
        · have hlt : (0 : Fin (k + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
          exact hi.2 j hlt
      · left
        intro j
        subst i
        by_cases hjlast : j = Fin.last k
        · subst j
          by_contra hnot
          let p : Fin (k + 1) := ⟨k - 1, by omega⟩
          have hprev : signSeqDoor s p := by
            exact signSeqDoor_prev_of_bad hi
              ((signSeq_bad_iff_not_altPos s (Fin.last k)).mpr hnot)
              (by simp [Fin.last]; omega)
          have hprev_mem : p ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hprev
          have hne : p ≠ Fin.last k := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [p] at hv
            simp [Fin.last] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hprev_mem, Fin.last k, hi_mem, hne⟩
          omega
        · have hlt : j < Fin.last k := Fin.lt_last_iff_ne_last.mpr hjlast
          exact hi.1 j hlt
  · intro h
    rcases h with hpos | hneg
    · rw [signSeqDoorSet_eq_singleton_last_of_altPos hpos]
      simp
    · rw [signSeqDoorSet_eq_singleton_zero_of_altNeg hneg]
      simp
