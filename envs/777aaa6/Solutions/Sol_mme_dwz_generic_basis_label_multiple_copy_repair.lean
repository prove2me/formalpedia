-- Prove2me | solution 1 for mme_dwz_generic_basis_label_multiple_copy_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T10:03:31.226507+00:00
-- url     : https://prove2.me/submissions/e9cdd5d5-1224-421a-9e8e-6161b1826f2f

import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_dwz_greedy_item_grouping
import Theorems.Thm_mme_bigAdd_list_flatten_isomorphic_nested
import Theorems.Thm_mme_bigAdd_list_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MME Module PiTensorProduct
open MME.DWZComponentRestriction MME.DWZSquare
open scoped BigOperators
universe u v w z
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace MME.DWZManyCopyRepair

theorem nonholeFraction_bounds {Block : Type w} [Fintype Block]
    [Nonempty Block] (copy : BrokenBlockCopy Block) :
    0 ≤ nonholeFraction copy ∧ nonholeFraction copy ≤ 1 := by
  have hpos : (0 : ℝ) < Fintype.card Block := by
    exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hpos)
  · apply (div_le_one hpos).mpr
    exact_mod_cast Finset.card_le_univ copy.nonholes

theorem sum_get_eq {Item : Type} (items : List Item) (f : Item → ℝ) :
    (∑ i : Fin items.length, f (items.get i)) = (items.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_comp' _ _ |>.trans (by rw [List.ofFn_get])

theorem bigAdd_cast {K : Type u} [Field K] {n m : ℕ}
    (h : n = m) (X : Fin m → TensorObj K 3) :
    TensorObj.bigAdd (fun i : Fin n ↦ X (Fin.cast h i)) = TensorObj.bigAdd X := by
  subst m
  rfl

theorem generic_multiple_copy_repair
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι : Type z} {Block : Type w} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : Basis ι K (X.V 2)) (label : ι → Block)
    (system : AvailableBlockShuffle Block Shuffle)
    (shuffleMap : Shuffle → ∀ i, X.V i →ₗ[K] X.V i)
    (basisPerm : Shuffle → Equiv.Perm ι)
    (hZ : ∀ g i, shuffleMap g 2 (b i) = b (basisPerm g i))
    (hlabel : ∀ g i, label (basisPerm g i) = system.move g (label i))
    (hX : ∀ g, PiTensorProduct.map (shuffleMap g) X.t = X.t)
    (N ell s r : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : (r : ℝ) * ((N * ell + 2 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let source : Fin s → TensorObj K 3 := fun t ↦
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label (copies t).nonholes)) X.t }
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin r ↦ X))
      (TensorObj.bigAdd source) := by
  classical
  dsimp only
  let source : Fin s → TensorObj K 3 := fun t ↦
    { V := X.V
      t := PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label (copies t).nonholes)) X.t }
  let weight : Fin s → ℝ := fun t ↦ nonholeFraction (copies t)
  have hL : (0 : ℝ) < (N * ell + 1 : ℕ) := by positivity
  have hbudget : (r : ℝ) * (((N * ell + 1 : ℕ) : ℝ) + 1) ≤
      ((List.finRange s).map weight).sum := by
    simpa only [← List.ofFn_eq_map, List.sum_ofFn, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hsum
  obtain ⟨groups, remainder, hitems, hlength, hgroups⟩ :=
    mme_dwz_greedy_item_grouping weight (List.finRange s)
      (fun j _ ↦ (nonholeFraction_bounds (copies j)).1)
      (fun j _ ↦ (nonholeFraction_bounds (copies j)).2)
      ((N * ell + 1 : ℕ) : ℝ) hL r hbudget
  have hgroup (a : Fin groups.length) : TensorObj.Restrict X
      (TensorObj.bigAdd (fun j : Fin (groups.get a).length ↦
        source ((groups.get a).get j))) := by
    have hm := (hgroups (groups.get a) (List.get_mem groups a)).1
    have hm' : ((N * ell + 1 : ℕ) : ℝ) ≤
        ∑ j : Fin (groups.get a).length,
          nonholeFraction (copies ((groups.get a).get j)) := by
      exact hm.trans_eq (sum_get_eq (groups.get a) weight).symm
    obtain ⟨_, _, _, _, _, _, _, hrepair⟩ :=
      mme_dwz_generic_basis_label_hole_cover_tensor_repair X b label system
        shuffleMap basisPerm hZ hlabel hX N ell (groups.get a).length hN hell
        (fun j ↦ copies ((groups.get a).get j)) hcard hm'
    exact hrepair
  have hflatten :=
    (mme_bigAdd_list_flatten_isomorphic_nested groups source).2
  have hprefix := mme_bigAdd_list_prefix_restrict (by decide : 1 < 3)
    source groups.flatten remainder
  have hprefix' : TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin groups.flatten.length ↦
        source (groups.flatten.get i)))
      (TensorObj.bigAdd (fun i : Fin (List.finRange s).length ↦
        source ((List.finRange s).get i))) := by
    rw [hitems]
    exact hprefix
  have hall := (mme_bigAdd_mono_restrict hgroup).trans
    (hflatten.trans hprefix')
  subst r
  have hlist :
      (TensorObj.bigAdd (fun i : Fin (List.finRange s).length ↦
        source ((List.finRange s).get i))) = TensorObj.bigAdd source := by
    simpa only [List.get_eq_getElem, List.getElem_finRange] using
      bigAdd_cast (List.length_finRange (n := s)) source
  rw [hlist] at hall
  exact hall

end MME.DWZManyCopyRepair

theorem solution
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι : Type z} {Block : Type w} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : Basis ι K (X.V 2)) (label : ι → Block)
    (system : AvailableBlockShuffle Block Shuffle)
    (shuffleMap : Shuffle → ∀ i, X.V i →ₗ[K] X.V i)
    (basisPerm : Shuffle → Equiv.Perm ι)
    (hZ : ∀ g i, shuffleMap g 2 (b i) = b (basisPerm g i))
    (hlabel : ∀ g i, label (basisPerm g i) = system.move g (label i))
    (hX : ∀ g, PiTensorProduct.map (shuffleMap g) X.t = X.t)
    (N ell s r : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : (r : ℝ) * ((N * ell + 2 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let source : Fin s → TensorObj K 3 := fun t ↦
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label (copies t).nonholes)) X.t }
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin r ↦ X))
      (TensorObj.bigAdd source) := by
  exact MME.DWZManyCopyRepair.generic_multiple_copy_repair X b label system
    shuffleMap basisPerm hZ hlabel hX N ell s r hN hell copies hcard hsum

