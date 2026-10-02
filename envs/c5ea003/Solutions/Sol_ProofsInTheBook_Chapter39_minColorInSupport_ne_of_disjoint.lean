-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.minColorInSupport_ne_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:22.458242+00:00
-- url     : https://prove2.me/submissions/c7b2783d-2122-4481-b194-034443505af8

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















theorem exists_kneserVertexIn_color_eq_minColorInSupport {n k q : ℕ}
    (C : KneserVertex n k → Fin q) {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    ∃ A : KneserVertexIn n k support, C A.1 = minColorInSupport C support hcard := by
  classical
  have hmem :
      minColorInSupport C support hcard ∈ colorsInSupport C support :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨A, _hA, hAeq⟩
  exact ⟨A, hAeq⟩

















































































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

theorem solution {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by
  classical
  obtain ⟨A, hAcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hleft
  obtain ⟨B, hBcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hright
  have hABdisj : Disjoint (A.1.1 : Finset (Fin n)) (B.1.1 : Finset (Fin n)) :=
    Disjoint.mono A.2 B.2 hdisj
  have hABne : A.1 ≠ B.1 := by
    intro h
    have hself : Disjoint (A.1.1 : Finset (Fin n)) (A.1.1 : Finset (Fin n)) := by
      simpa [h] using hABdisj
    have hempty : (A.1.1 : Finset (Fin n)) = ∅ := by
      exact (Finset.disjoint_self_iff_empty _).mp hself
    have hzero : (A.1.1 : Finset (Fin n)).card = 0 := by simp [hempty]
    have hAcard : (A.1.1 : Finset (Fin n)).card = k := A.1.2
    omega
  intro hmin
  exact hC A.1 B.1 ⟨hABne, hABdisj⟩ (hAcolor.trans (hmin.trans hBcolor.symm))
