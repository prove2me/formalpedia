-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.signSeqDoor_iff_remove_altPos
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:09:40.001072+00:00
-- url     : https://prove2.me/submissions/e64f6403-7f63-48c9-98f6-1249f0b1370d

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



















theorem signSeq_not_even_succ_decide (a : ℕ) :
    (!decide (Even (a + 1))) = decide (Even a) := by
  by_cases ha : Even a <;> simp [ha, Nat.even_add_one]





















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

theorem solution {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a)) := by
  constructor
  · intro h a
    by_cases hlt : i.succAbove a < i
    · have hs := h.1 (i.succAbove a) hlt
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hlt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : (i.succAbove a).val = a.val := by
        rw [hsa]
        rfl
      simpa [hval] using hs
    · have hgt : i < i.succAbove a := by
        have hne : i ≠ i.succAbove a := Fin.ne_succAbove i a
        exact lt_of_le_of_ne (le_of_not_gt hlt) hne
      have hs := h.2 (i.succAbove a) hgt
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hgt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : (i.succAbove a).val = a.val + 1 := by
        rw [hsa]
        rfl
      change s (i.succAbove a) = decide (Even a.val)
      rw [hs, hval]
      exact signSeq_not_even_succ_decide a.val
  · intro h
    constructor
    · intro j hji
      have hne : j ≠ i := ne_of_lt hji
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_lt : i.succAbove a < i := by
        simpa [ha] using hji
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hsa_lt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : a.val = j.val := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      simpa [hval] using hs_j
    · intro j hij
      have hne : j ≠ i := ne_of_gt hij
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_gt : i < i.succAbove a := by
        simpa [ha] using hij
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hsa_gt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : j.val = a.val + 1 := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv.symm
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      rw [hs_j, hval]
      exact (signSeq_not_even_succ_decide a.val).symm
