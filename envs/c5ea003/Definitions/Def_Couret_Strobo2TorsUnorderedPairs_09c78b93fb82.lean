-- Prove2me | Definitions.Def_Couret_Strobo2TorsUnorderedPairs_09c78b93fb82
-- name    : Couret_Strobo2TorsUnorderedPairs_09c78b93fb82
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:18.990131+00:00
-- url     : https://prove2.me/theorems/1e92e88f-15b3-47d5-bd14-213dd64ae078
-- title:
--   An unordered graph of nontranslated square collisions
-- statement:
--   Let $G$ be a finite abelian group. The simple graph has all finite supports as its vertex type. Its active edges join three-element supports $S,T$ with identical labelled ordered-sum counts and no $u\in G$ satisfying $T=S+u$. Nontriples are isolated, and equal supports cannot be adjacent because translation by zero is available. The bundle provides finite-neighbour instances and defines the unordered collision count as the finite edge-set cardinality, with the endpoint-exchange symmetry already quotiented by the graph edge representation. There is no additional zero-avoidance restriction in this graph definition.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/3fb45e3419d8f464ba08064afe59061c6f6f9189/research/strobo-2tors-2026-10-12/lean/Strobo2TorsUnorderedPairs.lean; source file SHA-256 0a0634b10b5614f2bdf375961002c86d0995bc2a8ad571bab13c0dd8918d2528

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The graph whose vertices are finite supports.  An edge joins two genuine
three-element supports with identical labelled ordered squares and no
ambient translation between them.  The vertex universe also includes
non-triples, but those are isolated by construction. -/
noncomputable def nontranslationPairGraph : SimpleGraph (Finset G) where
  Adj S T := S.card = 3 ∧ T ∈ nontranslatedNeighbours S
  symm := by
    intro S T h
    obtain ⟨hS, hT⟩ := h
    obtain ⟨hTcard, hEq, hNoTranslate⟩ :=
      (mem_nontranslatedNeighbours S T hS).mp hT
    refine ⟨hTcard, (mem_nontranslatedNeighbours T S hTcard).mpr ?_⟩
    refine ⟨hS, (fun z => (hEq z).symm), ?_⟩
    rintro ⟨u, hReverse⟩
    apply hNoTranslate
    refine ⟨-u, ?_⟩
    calc
      T = translateSupport T (0 : G) := by simp [translateSupport]
      _ = translateSupport T (u + (-u)) := by simp
      _ = translateSupport (translateSupport T u) (-u) :=
        (translateSupport_add T u (-u)).symm
      _ = translateSupport S (-u) := by rw [hReverse]
  loopless := ⟨by
    intro S h
    obtain ⟨hS, hSelf⟩ := h
    have hNo := ((mem_nontranslatedNeighbours S S hS).mp hSelf).2.2
    exact hNo ⟨0, by simp [translateSupport]⟩⟩

/-- Finiteness of the ambient support type gives finite neighbour sets.
Using `Fintype.ofFinite` is safe but intentionally noncomputable. -/
noncomputable instance nontranslationGraphNeighborFintype (S : Finset G) :
    Fintype ((nontranslationPairGraph (G := G)).neighborSet S) := by
  classical
  exact (nontranslationPairGraph (G := G)).neighborSetFintype S













/-- Number of genuine unordered pairs. A SimpleGraph edge uses Sym2,
so the off-diagonal involution has already been quotiented correctly. -/
noncomputable def nontranslationUnorderedPairCount : ℕ := by
  classical
  exact (nontranslationPairGraph (G := G)).edgeFinset.card





end Couret.STROBO2TORS


