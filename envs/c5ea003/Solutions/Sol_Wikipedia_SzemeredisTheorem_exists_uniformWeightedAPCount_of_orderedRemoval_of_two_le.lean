-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:57:14.883221+00:00
-- url     : https://prove2.me/submissions/4e3442ec-6cb6-4163-b44d-d5794fc83f9c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_uniformDenseAPCount_of_simplexRemoval
import Theorems.Thm_Wikipedia_SzemeredisTheorem_hasUniformCyclicPartiteSimplexRemoval_of_ordered
import Theorems.Thm_Wikipedia_SzemeredisTheorem_weightedAPCount_of_denseAPCount

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





























namespace SimplexHypergraph







end SimplexHypergraph























/-- The thresholding argument upgrades the set-valued consequence of
simplex removal to bounded weights, retaining a positive uniform constant. -/
theorem exists_uniformWeightedAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c := by
  obtain ⟨c₀, hc₀, hdense⟩ :=
    exists_uniformDenseAPCount_of_simplexRemoval
      r hrem (half_pos hδ)
  refine ⟨(δ / 2) ^ (r + 2) * c₀, ?_, ?_⟩
  · exact mul_pos (pow_pos (half_pos hδ) _) hc₀
  · intro N inst g hg0 hg1 hmean
    exact weightedAPCount_of_denseAPCount
      hδ.le (hdense N) hg0 hg1 hmean

end Wikipedia.SzemeredisTheorem

end

section




/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









































/-- The successor-indexed bridge in the arithmetic-progression convention:
rank `r + 1` ordered removal on `r + 2` classes supplies the
`r + 2`-colour simplex-removal input. -/
theorem hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1)) :
    HasUniformCyclicPartiteSimplexRemoval (r + 2) := by
  simpa [Nat.add_assoc] using
    (hasUniformCyclicPartiteSimplexRemoval_of_ordered
      (r + 1) (by simpa [Nat.add_assoc] using hordered))

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Dense Szemerédi consequences of ordered hypergraph removal

The equal-vertex bridge turns ordered rank-`r + 1` removal on `r + 2`
classes into cyclic partite simplex removal.  The standard arithmetic-
progression hypergraph construction then gives uniform dense and weighted
Szemerédi bounds.
-/

namespace Wikipedia.SzemeredisTheorem



/-- The same ordered-removal hypothesis gives the corresponding uniform
weighted cyclic Szemerédi bound. -/
theorem exists_uniformWeightedAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c :=
  exists_uniformWeightedAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ





end Wikipedia.SzemeredisTheorem

end
/-!
# Dense Szemerédi consequences of ordered hypergraph removal

The equal-vertex bridge turns ordered rank-`r + 1` removal on `r + 2`
classes into cyclic partite simplex removal.  The standard arithmetic-
progression hypergraph construction then gives uniform dense and weighted
Szemerédi bounds.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- A length-indexed formulation of the weighted consequence. -/
theorem solution
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformWeightedAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)
