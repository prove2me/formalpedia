-- Prove2me | solution 1 for mme_complete_split_exact_product_finite_hole_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:37:11.3875+00:00
-- url     : https://prove2.me/submissions/e48f4279-e4ae-4061-b664-073393307350

import Theorems.Thm_mme_complete_split_exact_restrictedPower_uniform_basis_interface
import Theorems.Thm_mme_modern_three_mode_finite_hole_repair
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_tensor_quotient
import Mathlib.Data.Fintype.BigOperators

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZSquare MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u v w

set_option autoImplicit false
set_option warningAsError true

private theorem product_uniform_shuffle
    {J : Type u} [Fintype J] [DecidableEq J]
    {Block : J → Type v} {Shuffle : J → Type w}
    [∀ j, Fintype (Block j)] [∀ j, DecidableEq (Block j)]
    [∀ j, Fintype (Shuffle j)] [∀ j, DecidableEq (Shuffle j)]
    (system : ∀ j, AvailableBlockShuffle (Block j) (Shuffle j)) :
    ∃ combined : AvailableBlockShuffle (∀ j, Block j) (∀ j, Shuffle j),
      ∀ g x j, combined.move g x j = (system j).move (g j) (x j) := by
  classical
  let move : (∀ j, Shuffle j) → Equiv.Perm (∀ j, Block j) :=
    fun g ↦ Equiv.piCongrRight (fun j ↦ (system j).move (g j))
  have huniform : ∀ source target : (∀ j, Block j),
      (Finset.univ.filter (fun g ↦ move g source = target)).card *
          Fintype.card (∀ j, Block j) = Fintype.card (∀ j, Shuffle j) := by
    intro source target
    have hset :
        Finset.univ.filter (fun g ↦ move g source = target) =
        Fintype.piFinset (fun j ↦ Finset.univ.filter
          (fun g : Shuffle j ↦ (system j).move g (source j) = target j)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      change (fun j ↦ (system j).move (g j) (source j)) = target ↔ _
      exact funext_iff
    rw [hset, Fintype.card_piFinset, Fintype.card_pi,
      ← Finset.prod_mul_distrib]
    simp only [AvailableBlockShuffle.uniform_fiber, Fintype.card_pi]
  exact ⟨⟨move, huniform⟩, fun _ _ _ ↦ rfl⟩

private theorem literal_restrict_projected_univ
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (label : ∀ i, I i → Label i) :
    TensorObj.Restrict T (projected T b label (fun _ ↦ Finset.univ)) := by
  have hproj : (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) =
      (fun i ↦ LinearMap.id (R := K) (M := T.V i)) := by
    funext i
    apply (b i).ext
    intro x
    simp [basisLabelProjection, Basis.constr_basis]
  refine ⟨fun _ ↦ LinearMap.id, ?_⟩
  change PiTensorProduct.map (fun i ↦ LinearMap.id (R := K) (M := T.V i))
    (PiTensorProduct.map
      (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) T.t) = T.t
  rw [hproj]
  simp only [PiTensorProduct.map_id, LinearMap.id_apply]

theorem solution
    {K : Type u} [Field K] {r : ℕ}
    (T : Fin r → TensorObj K 3) {I : Fin r → Fin 3 → Type u}
    (b : ∀ t i, Basis (I t i) K ((T t).V i)) {ell : ℕ}
    (label : ∀ t i, I t i → CompleteWord ell)
    (n : Fin r → ℕ) (beta : Fin r → Fin 3 → Profile ell) :
    let Coord := fun t i ↦
      {w : PowIndex (I t i) (n t) // ApproxConsistent (label t i) (beta t i) 0 w}
    let Block := fun t i ↦
      {w : PowIndex (CompleteWord ell) (n t) // ApproxConsistent id (beta t i) 0 w}
    let Term := fun t ↦ restrictedPower (T t) (b t) (label t) (beta t) 0 (n t)
    let G := fun t ↦ ((T t).kronPow (n t)).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis (T t) i (b t i) (n t))
      (fun i ↦ ApproxConsistent (label t i) (beta t i) 0)
    let S := TensorObj.kronFin r Term
    ∃ B : ∀ t i, Basis (Coord t i) K ((Term t).V i),
    ∃ blockLabel : ∀ t i, Coord t i → Block t i,
      (∀ t i w, ((G t).classOf i 0).subtype (B t i w) =
        kronPowModeBasis (T t) i (b t i) (n t) w.1) ∧
      (∀ t i w, (blockLabel t i w).1 =
        PowIndex.ofFun (n t) (fun j ↦ label t i (PowIndex.get (n t) w.1 j))) ∧
      ∀ d h : ℕ,
        (∏ i : Fin 3, Fintype.card (∀ t : Fin r, Block t i)) < d ^ h →
        ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (∀ t : Fin r, Block t i),
          (∀ a i, 4 * d * (holes a i).card ≤
            Fintype.card (∀ t : Fin r, Block t i)) →
          TensorObj.Restrict S
            (TensorObj.bigAdd (fun a ↦ projected S
              (fun i ↦ kronFinModePiBasis r Term i (fun t ↦ B t i))
              (fun i w t ↦ blockLabel t i (w t))
              (fun i ↦ Finset.univ \ holes a i))) := by
  classical
  let Coord := fun t i ↦
    {w : PowIndex (I t i) (n t) // ApproxConsistent (label t i) (beta t i) 0 w}
  let Block := fun t i ↦
    {w : PowIndex (CompleteWord ell) (n t) // ApproxConsistent id (beta t i) 0 w}
  let Term := fun t ↦ restrictedPower (T t) (b t) (label t) (beta t) 0 (n t)
  let S := TensorObj.kronFin r Term
  choose B blockLabel system hB hlabel hsystem haction using
    fun t ↦ mme_complete_split_exact_restrictedPower_uniform_basis_interface
      (T t) (b t) (label t) (beta t) (n t)
  refine ⟨B, blockLabel, hB, hlabel, ?_⟩
  intro d h hcapacity holes hholes
  choose Ψ basisImage ht hindex hbasis hactionlabel using haction
  have hprod := fun i : Fin 3 ↦ product_uniform_shuffle (fun t ↦ system t i)
  choose productSystem hproductSystem using hprod
  let productBasis : ∀ i, Basis (∀ t, Coord t i) K (S.V i) :=
    fun i ↦ kronFinModePiBasis r Term i (fun t ↦ B t i)
  let productLabel : ∀ i, (∀ t, Coord t i) → (∀ t, Block t i) :=
    fun i x t ↦ blockLabel t i (x t)
  let maps : (∀ t, Equiv.Perm (Fin (n t))) → ∀ i, S.V i →ₗ[K] S.V i :=
    fun g ↦ kronFinFamilyModeMap r Term Term (fun t i ↦ (Ψ t (g t) i).toLinearMap)
  let image : (∀ t, Equiv.Perm (Fin (n t))) → ∀ i, (∀ t, Coord t i) → (∀ t, Coord t i) :=
    fun g i x t ↦ basisImage t (g t) i (x t)
  have hmapbasis : ∀ g i x, maps g i (productBasis i x) =
      productBasis i (image g i x) := by
    intro g i x
    exact kronFinFamilyModeMap_basis Term Term i (fun t ↦ B t i) (fun t ↦ B t i)
      (fun t j ↦ (Ψ t (g t) j).toLinearMap)
      (fun t ↦ basisImage t (g t) i) (fun t y ↦ hbasis t (g t) i y) x
  have hmaplabel : ∀ g i x,
      productLabel i (image g i x) = (productSystem i).move g (productLabel i x) := by
    intro g i x
    funext t
    exact (hactionlabel t (g t) i (x t)).trans
      (hproductSystem i g (productLabel i x) t).symm
  have hmaptensor : ∀ g, PiTensorProduct.map (maps g) S.t = S.t := by
    intro g
    exact kronFinFamilyModeMap_preserves_tensor Term Term
      (fun t i ↦ (Ψ t (g t) i).toLinearMap) (fun t ↦ ht t (g t))
  have hrepair := mme_modern_three_mode_finite_hole_repair S productBasis productLabel
    productSystem maps image hmapbasis hmaplabel hmaptensor d h
    (fun _ ↦ Finset.univ) holes hholes
    (by simpa only [Finset.card_univ] using hcapacity)
  exact (literal_restrict_projected_univ S productBasis productLabel).trans hrepair
