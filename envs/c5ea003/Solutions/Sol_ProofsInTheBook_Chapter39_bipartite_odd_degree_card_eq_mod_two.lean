-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.bipartite_odd_degree_card_eq_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:16.318902+00:00
-- url     : https://prove2.me/submissions/3e07eb7b-f56c-4550-b818-c50d72ac91a7

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









































/-! ### Sorted label-sequence deletion parity -/

























































/-! ## Ky Fan parity statement on the non-degenerate range -/















































































/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/

theorem finset_card_filter_cast_zmod_two {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ZMod 2) =
      ∑ x ∈ s, if p x then (1 : ZMod 2) else 0 := by
  rw [Finset.sum_boole]

theorem fintype_card_subtype_cast_zmod_two {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (Fintype.card {x : α // p x} : ZMod 2) =
      ∑ x : α, if p x then (1 : ZMod 2) else 0 := by
  classical
  rw [← finset_card_filter_cast_zmod_two (Finset.univ : Finset α) p]
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (Fintype.card_subtype p)







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

theorem solution
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by
  classical
  rw [fintype_card_subtype_cast_zmod_two, fintype_card_subtype_cast_zmod_two]
  calc
    (∑ r : R, if Odd (Fintype.card {s : S // edge r s}) then (1 : ZMod 2) else 0)
        = ∑ r : R, (Fintype.card {s : S // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hodd : Odd (Fintype.card {s : S // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two.symm
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {s : S // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two.symm
    _ = ∑ r : R, ∑ s : S, if edge r s then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [← fintype_card_subtype_cast_zmod_two (fun s : S => edge r s)]
    _ = ∑ s : S, ∑ r : R, if edge r s then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (Fintype.card {r : R // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          rw [← fintype_card_subtype_cast_zmod_two (fun r : R => edge r s)]
    _ = ∑ s : S, if Odd (Fintype.card {r : R // edge r s}) then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          by_cases hodd : Odd (Fintype.card {r : R // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {r : R // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two
