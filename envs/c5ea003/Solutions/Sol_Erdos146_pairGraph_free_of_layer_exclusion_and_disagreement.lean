-- Prove2me | solution 1 for Erdos146.pairGraph_free_of_layer_exclusion_and_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:41:45.613675+00:00
-- url     : https://prove2.me/submissions/8ad8612b-9909-4a6f-b4f5-dcdd6ff80012

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Theorems.Thm_Erdos146_binaryEntropy_le_one
import Theorems.Thm_Erdos146_binaryEntropy_nonneg
import Theorems.Thm_Erdos146_pairGraphCopy_child_layer_side_eq
import Theorems.Thm_Erdos146_pairGraphCopy_layer_entropy_upper_of_disagreement

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem entropy_potential_increment
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < entropySlack)
    (hlower : midpointBeta - entropySlack < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpoint +
        (potentialAfter - potentialBefore) / 2 + error) :
    certifiedWindowWidth / 2 < potentialAfter - potentialBefore := by
  have hwindow := entropyWindow_eq_certifiedWindowWidth
  unfold midpointBeta entropySlack at hlower
  unfold entropySlack at herror
  linarith

theorem entropy_potential_layers_impossible
    (depth : ℕ) (potential : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth,
      certifiedWindowWidth / 2 < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  have htotal :
      ∀ i ≤ depth,
        (i : ℝ) * (certifiedWindowWidth / 2) ≤
          potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiprev : i ≤ depth := by omega
        have histep : i < depth := by omega
        have hprevious := ih hiprev
        have hnext := (hincrement i histep).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith

theorem entropy_layer_exclusion
    (depth : ℕ) (potential conditionalEntropy error : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (herror : ∀ i < depth, error i < entropySlack)
    (hlower : ∀ i < depth,
      midpointBeta - entropySlack < conditionalEntropy i)
    (hupper : ∀ i < depth,
      conditionalEntropy i ≤
        entropyLowerEndpoint +
          (potential (i + 1) - potential i) / 2 + error i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  apply entropy_potential_layers_impossible depth potential hrange
    (hdepth := hdepth)
  intro i hi
  exact entropy_potential_increment (potential i) (potential (i + 1))
    (conditionalEntropy i) (error i)
    (herror i hi) (hlower i hi) (hupper i hi)

theorem pairLayerPair_nonempty
    {parentCount : ℕ}
    (hparents : 2 ≤ parentCount) :
    Nonempty (PairLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [pairLayer_card_succ parentCount 0,
    pairLayer_card_zero]
  exact Nat.choose_pos hparents

theorem pairGraphCopyLayerPotential_mem_Icc
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ pairGraphCopyLayerPotential retained copy layer ∧
      pairGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer :
      0 < Fintype.card (PairLayer baseSize layer.val) := by
    have hcard := pairLayer_card_ge_base
      baseSize layer.val hbase
    omega
  have hlayer_real :
      0 < (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card ≤
          Fintype.card (PairLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (PairLayer baseSize layer.val))
          (fun vertex =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate = true))
    have hzero :
        0 ≤
          ((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
      positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone,
      binaryEntropy_le_one _⟩
  unfold pairGraphCopyLayerPotential
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg
        (fun coordinate _ => (hterm coordinate).1)
    · exact hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc
      (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun coordinate _ => (hterm coordinate).2)
      _ = (dimension : ℝ) := by
        simp

theorem pairGraphCopyChildWords_injective
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) first)
    ((pairLayerPairEquiv baseSize layer.val) second)
  have hvertices :
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first))).val =
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second))).val := by
    apply Prod.ext
    · exact hside
    · exact hwords
  have himages :
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first)) =
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have hpairs :=
    (pairLayerEmbedding baseSize depth (layer.val + 1)
      (by omega)).injective hsources
  exact (pairLayerPairEquiv baseSize layer.val).injective hpairs

theorem pairGraphCopyChildWords_retained
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) :
    retained ∈
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference)
        (pairGraphCopyChildWords retained copy layer) := by
  intro pair
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) reference)
    ((pairLayerPairEquiv baseSize layer.val) pair)
  have hretained :=
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).property
  change
    (pairGraphCopyChildSide retained copy layer reference,
      pairGraphCopyChildWords retained copy layer pair) ∈ retained
  unfold pairGraphCopyChildSide pairGraphCopyChildWords
  rw [hside]
  exact hretained

theorem pairGraphCopy_entropy_lower_of_exclusion
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        badPairLayerRetentionEvent
          (Fintype.card (PairLayer baseSize layer.val)) dimension
          (pairGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ threshold :=
    le_of_not_gt hnot
  have hbad_array :
      pairGraphCopyChildWords retained copy layer ∈
        badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold := by
    unfold badPairChildArrays
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      pairGraphCopyChildWords retained copy layer ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array,
        pairGraphCopyChildWords_injective retained copy layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (PairLayer baseSize layer.val)) →
          HammingWord dimension,
      badPairChildRetentionEvent parents
        (pairGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨pairGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨pairGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          pairGraphCopyChildWords_retained
            retained copy layer reference⟩⟩

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairParentSystem baseSize depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let potential : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth + 1 then
      pairGraphCopyLayerPotential retained copy ⟨layer, hlevel⟩
    else 0
  let conditionalEntropy : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy ⟨layer, hlevel⟩)
        (pairGraphCopyChildWords retained copy ⟨layer, hlevel⟩)
    else 0
  let error : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      empiricalEntropyError
        (Fintype.card (PairLayer baseSize layer))
    else 0
  apply entropy_layer_exclusion depth
    potential conditionalEntropy error
  · intro layer hlayer
    have hinrange : layer < depth + 1 := by omega
    have hle : layer ≤ depth := by omega
    simpa [potential, hinrange, hle] using
      pairGraphCopyLayerPotential_mem_Icc
        hbase hdimension retained copy ⟨layer, hinrange⟩
  · intro layer hlayer
    simpa [error, hlayer] using
      herror ⟨layer, hlayer⟩
  · intro layer hlayer
    have hsize :
        2 ≤ Fintype.card (PairLayer baseSize layer) := by
      have hcard := pairLayer_card_ge_base
        baseSize layer hbase
      omega
    let reference :
        PairLayer (Fintype.card (PairLayer baseSize layer)) 1 :=
      Classical.choice (pairLayerPair_nonempty hsize)
    have hlower := pairGraphCopy_entropy_lower_of_exclusion
      retained copy ⟨layer, hlayer⟩ reference
        (midpointBeta - entropySlack)
        (hexclusion
          (pairGraphCopyChildSide
            retained copy ⟨layer, hlayer⟩ reference)
          ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, hlayer] using hlower
  · intro layer hlayer
    have hnext : layer + 1 < depth + 1 := by omega
    have hcurrent : layer < depth + 1 := by omega
    have hnext_le : layer + 1 ≤ depth := by omega
    have hcurrent_le : layer ≤ depth := by omega
    have hupper := pairGraphCopy_layer_entropy_upper_of_disagreement
      hbase hdimension retained copy ⟨layer, hlayer⟩
      (hdisagreement copy ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, potential, error,
      hlayer, hnext, hcurrent, hnext_le, hcurrent_le] using hupper
  · exact hdepth
