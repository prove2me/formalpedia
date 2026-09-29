-- Prove2me | solution 1 for mme_modern_three_mode_finite_hole_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:17:21.054493+00:00
-- url     : https://prove2.me/submissions/b2c9dc6a-bf54-4cbc-a372-1d260087e49a

import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_tensor_rank
import Theorems.Thm_mme_bigAdd_map_sum_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_modern_three_mode_common_shuffle_intersection_bound
import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open MME Module PiTensorProduct BigOperators
open MME.DWZComponentRestriction MME.DWZSquare

universe u v w

set_option autoImplicit false
set_option warningAsError true

namespace MME.ModernRepair

private theorem shuffled_broken_projects_to_retained
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (maps : (i : Fin 3) → T.V i →ₗ[K] T.V i)
    (basisImage : (i : Fin 3) → ι i → ι i)
    (move : (i : Fin 3) → Equiv.Perm (Label i))
    (hbasis : ∀ i x, maps i (b i x) = b i (basisImage i x))
    (hlabel : ∀ i x, label i (basisImage i x) = move i (label i x))
    (htensor : PiTensorProduct.map maps T.t = T.t)
    (P Q : (i : Fin 3) → Finset (Label i)) :
    TensorObj.Restrict
      (projected T b label (fun i ↦ P i \ (Q i).image (move i)))
      (projected T b label (fun i ↦ Finset.univ \ Q i)) := by
  classical
  let f : (i : Fin 3) → T.V i →ₗ[K] T.V i :=
    fun i ↦ (basisLabelProjection (b i) (label i) (P i)).comp (maps i)
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f
      (PiTensorProduct.map
        (fun i ↦ basisLabelProjection (b i) (label i) (Finset.univ \ Q i)) T.t) =
    PiTensorProduct.map
      (fun i ↦ basisLabelProjection (b i) (label i) (P i \ (Q i).image (move i))) T.t
  have hmaps : ∀ i,
      (f i).comp (basisLabelProjection (b i) (label i) (Finset.univ \ Q i)) =
        (basisLabelProjection (b i) (label i) (P i \ (Q i).image (move i))).comp
          (maps i) := by
    intro i
    apply (b i).ext
    intro x
    by_cases hp : move i (label i x) ∈ P i <;>
      by_cases hq : label i x ∈ Q i <;>
      simp [f, LinearMap.comp_apply, basisLabelProjection, Basis.constr_basis,
        hbasis, hlabel, hp, hq]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simp_rw [hmaps]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, htensor]

end MME.ModernRepair

namespace MME.ModernRepair

private theorem product_shrink_of_one_coordinate
    (d : ℕ) (a b : Fin 3 → ℕ)
    (hle : ∀ i, a i ≤ b i) (i : Fin 3)
    (hshrink : d * a i ≤ b i) :
    d * (∏ j : Fin 3, a j) ≤ ∏ j : Fin 3, b j := by
  calc
    d * (∏ j : Fin 3, a j) =
        (d * a i) * ∏ j ∈ Finset.univ.erase i, a j := by
      rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
      ring
    _ ≤ b i * ∏ j ∈ Finset.univ.erase i, b j :=
      Nat.mul_le_mul hshrink
        (Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun j _ ↦ hle j))
    _ = ∏ j : Fin 3, b j :=
      Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)

private theorem product_threshold_descends
    (d h volume child : ℕ)
    (hvolume : volume < d ^ (h + 1))
    (hchild : d * child ≤ volume) :
    child < d ^ h := by
  have hlt : d * child < d * d ^ h := by
    exact lt_of_le_of_lt hchild (by simpa only [Nat.pow_succ'] using hvolume)
  by_contra hnot
  have hge : d * d ^ h ≤ d * child :=
    Nat.mul_le_mul_left d (Nat.le_of_not_gt hnot)
  exact (not_lt_of_ge hge) hlt

private theorem hole_intersection_shrinks
    {Block : Type*} [Fintype Block] [DecidableEq Block]
    (d : ℕ) (P Q : Finset Block) (move : Equiv.Perm Block)
    (hintersection : (P ∩ Q.image move).card * Fintype.card Block ≤
      4 * (P.card * Q.card))
    (hholes : 4 * d * Q.card ≤ Fintype.card Block) :
    d * (P ∩ Q.image move).card ≤ P.card := by
  rcases Nat.eq_zero_or_pos (Fintype.card Block) with hzero | hpos
  · have hp : P.card = 0 := Nat.eq_zero_of_le_zero
      (by simpa only [hzero] using P.card_le_univ)
    simp [Finset.card_eq_zero.mp hp]
  · apply Nat.le_of_mul_le_mul_right (c := Fintype.card Block) _ hpos
    calc
      (d * (P ∩ Q.image move).card) * Fintype.card Block =
          d * ((P ∩ Q.image move).card * Fintype.card Block) := by ring
      _ ≤ d * (4 * (P.card * Q.card)) := Nat.mul_le_mul_left d hintersection
      _ = P.card * (4 * d * Q.card) := by ring
      _ ≤ P.card * Fintype.card Block := Nat.mul_le_mul_left P.card hholes

end MME.ModernRepair

namespace MME.ModernRepair

private theorem map_eq_zero_of_zero_coordinate
    {K : Type u} [Field K] {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : (i : Fin 3) → V i →ₗ[K] W i) (i : Fin 3)
    (hzero : f i = 0) (x : PiTensorProduct K V) :
    PiTensorProduct.map f x = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
      rw [map_smul, PiTensorProduct.map_tprod]
      have hi : f i (x i) = 0 := by simp [hzero]
      rw [(PiTensorProduct.tprod K).map_coord_zero i hi, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

private theorem projected_zero_of_empty_coordinate
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, DecidableEq (Label i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (P : (i : Fin 3) → Finset (Label i)) (i : Fin 3)
    (hP : P i = ∅) : (projected T b label P).t = 0 := by
  apply map_eq_zero_of_zero_coordinate _ i _ T.t
  apply (b i).ext
  intro x
  simp [basisLabelProjection, Basis.constr_basis, hP]

private theorem projected_restrict_of_zero_volume
    {K : Type u} [Field K] (T X : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, DecidableEq (Label i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (P : (i : Fin 3) → Finset (Label i))
    (hP : (∏ i : Fin 3, (P i).card) = 0) :
    TensorObj.Restrict (projected T b label P) X := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hP
  refine ⟨fun _ ↦ 0, ?_⟩
  exact (map_eq_zero_of_zero_coordinate (fun _ ↦ 0) 0 rfl X.t).trans
    (projected_zero_of_empty_coordinate T b label P i
      (Finset.card_eq_zero.mp hi)).symm

private theorem first_copy_restrict_bigAdd
    {K : Type u} [Field K] {n : ℕ} (hn : 0 < n)
    (X : Fin n → TensorObj K 3) :
    TensorObj.Restrict (X ⟨0, hn⟩) (TensorObj.bigAdd X) := by
  have h := mme_bigAdd_prefix_restrict (by decide : 1 < 3) hn X
  simpa only [TensorObj.bigAdd] using h

end MME.ModernRepair

open MME.ModernRepair

private theorem map_sum_binary_modes
    {K : Type u} [Field K]
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin 2 → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ ∑ j, f i j) x =
      ∑ js : Fin 3 → Fin 2,
        PiTensorProduct.map (fun i ↦ f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

private theorem label_projection_split
    {K : Type u} [Field K] {V : Type u}
    [AddCommGroup V] [Module K V]
    {ι : Type u} {Label : Type v} [DecidableEq Label]
    (b : Basis ι K V) (label : ι → Label) (P Q : Finset Label) :
    basisLabelProjection b label P =
      ∑ a : Fin 2, basisLabelProjection b label
        (if a = 0 then P ∩ Q else P \ Q) := by
  classical
  apply b.ext
  intro x
  simp only [Fin.sum_univ_two, LinearMap.add_apply,
    basisLabelProjection, Basis.constr_basis]
  by_cases hp : label x ∈ P <;> by_cases hq : label x ∈ Q <;> simp [hp, hq]

private theorem eight_box_projection_restrict
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, DecidableEq (Label i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (P Q : (i : Fin 3) → Finset (Label i))
    (enumerate : Fin 8 ≃ (Fin 3 → Fin 2)) :
    let box : (Fin 3 → Fin 2) → (i : Fin 3) → Finset (Label i) :=
      fun sigma i ↦ if sigma i = 0 then P i ∩ Q i else P i \ Q i
    TensorObj.Restrict (projected T b label P)
      (TensorObj.bigAdd (fun j : Fin 8 ↦ projected T b label (box (enumerate j)))) := by
  classical
  let pr := projected T b label
  let box : (Fin 3 → Fin 2) → (i : Fin 3) → Finset (Label i) :=
    fun sigma i ↦ if sigma i = 0 then P i ∩ Q i else P i \ Q i
  let F : (Fin 3 → Fin 2) → PiTensorProduct K T.V :=
    fun sigma ↦ (pr (box sigma)).t
  change TensorObj.Restrict (pr P)
    (TensorObj.bigAdd (fun j : Fin 8 ↦ pr (box (enumerate j))))
  have hall : (show PiTensorProduct K T.V from (pr P).t) = ∑ sigma, F sigma := by
    change PiTensorProduct.map
      (fun i ↦ basisLabelProjection (b i) (label i) (P i)) T.t = _
    have hmaps :
        (fun i ↦ basisLabelProjection (b i) (label i) (P i)) =
          fun i ↦ ∑ a : Fin 2, basisLabelProjection (b i) (label i)
            (if a = 0 then P i ∩ Q i else P i \ Q i) := by
      funext i
      exact label_projection_split (b i) (label i) (P i) (Q i)
    rw [hmaps]
    change PiTensorProduct.map
      (fun i ↦ ∑ a : Fin 2, basisLabelProjection (b i) (label i)
        (if a = 0 then P i ∩ Q i else P i \ Q i)) T.t =
      ∑ sigma : Fin 3 → Fin 2,
        PiTensorProduct.map
          (fun i ↦ basisLabelProjection (b i) (label i)
            (if sigma i = 0 then P i ∩ Q i else P i \ Q i)) T.t
    exact map_sum_binary_modes
      (fun i a ↦ basisLabelProjection (b i) (label i)
        (if a = 0 then P i ∩ Q i else P i \ Q i)) T.t
  have hsum :
      (∑ j : Fin 8, F (enumerate j)) =
        (show PiTensorProduct K T.V from (pr P).t) :=
    (Equiv.sum_comp enumerate F).trans hall.symm
  obtain ⟨maps, hmap⟩ := mme_bigAdd_map_sum_restrict
    (W := T.V)
    (fun j : Fin 8 ↦ pr (box (enumerate j)))
    (fun _ _ ↦ LinearMap.id)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
    (TensorObj.bigAdd (fun j : Fin 8 ↦ pr (box (enumerate j)))).t =
      (pr P).t
  change PiTensorProduct.map maps
    (TensorObj.bigAdd (fun j : Fin 8 ↦ pr (box (enumerate j)))).t =
      ∑ j : Fin 8, PiTensorProduct.map (fun _ ↦ LinearMap.id) (F (enumerate j)) at hmap
  have hid :
      (∑ j : Fin 8, PiTensorProduct.map (fun _ ↦ LinearMap.id)
        (F (enumerate j))) =
      ∑ j : Fin 8, F (enumerate j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [PiTensorProduct.map_id]
    rfl
  exact hmap.trans (hid.trans hsum)

private theorem bigAdd_cast_eq
    {K : Type u} [Field K] {m n : ℕ} (h : m = n)
    (X : Fin n → TensorObj K 3) :
    TensorObj.bigAdd (fun a : Fin m ↦ X (Fin.cast h a)) =
      TensorObj.bigAdd X := by
  subst n
  rfl

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v} {Shuffle : Type w}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (system : (i : Fin 3) → AvailableBlockShuffle (Label i) Shuffle)
    (maps : Shuffle → (i : Fin 3) → T.V i →ₗ[K] T.V i)
    (basisImage : Shuffle → (i : Fin 3) → ι i → ι i)
    (hbasis : ∀ g i x, maps g i (b i x) = b i (basisImage g i x))
    (hlabel : ∀ g i x,
      label i (basisImage g i x) = (system i).move g (label i x))
    (htensor : ∀ g, PiTensorProduct.map (maps g) T.t = T.t)
    (d : ℕ) :
    ∀ h : ℕ, ∀ P : (i : Fin 3) → Finset (Label i),
      ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Label i),
      (∀ a i, 4 * d * (holes a i).card ≤ Fintype.card (Label i)) →
      (∏ i : Fin 3, (P i).card) < d ^ h →
      TensorObj.Restrict (projected T b label P)
        (TensorObj.bigAdd (fun a ↦
          projected T b label (fun i ↦ Finset.univ \ holes a i))) := by
  classical
  let enumerate : Fin 8 ≃ (Fin 3 → Fin 2) :=
    (Fintype.equivFinOfCardEq
      (by decide : Fintype.card (Fin 3 → Fin 2) = 8)).symm
  intro h
  induction h with
  | zero =>
      intro P holes _ hvolume
      apply projected_restrict_of_zero_volume T _ b label P
      simpa only [pow_zero, Nat.lt_one_iff] using hvolume
  | succ h ih =>
      intro P holes hholes hvolume
      have hsize : 8 * 8 ^ h = 8 ^ (h + 1) := Nat.pow_succ'.symm
      let holes' : Fin (8 * 8 ^ h) → (i : Fin 3) → Finset (Label i) :=
        fun a ↦ holes (Fin.cast hsize a)
      have hholes' : ∀ a i, 4 * d * (holes' a i).card ≤ Fintype.card (Label i) :=
        fun a i ↦ hholes (Fin.cast hsize a) i
      have hc : 0 < 8 ^ h := pow_pos (by decide) h
      let kept : Fin 8 := enumerate.symm (fun _ ↦ 1)
      let Q : (i : Fin 3) → Finset (Label i) :=
        holes' (finProdFinEquiv (m := 8) (n := 8 ^ h) (kept, ⟨0, hc⟩))
      obtain ⟨g, hg⟩ :=
        mme_modern_three_mode_common_shuffle_intersection_bound system P Q
      let Qg : (i : Fin 3) → Finset (Label i) :=
        fun i ↦ (Q i).image ((system i).move g)
      let box : (Fin 3 → Fin 2) → (i : Fin 3) → Finset (Label i) :=
        fun sigma i ↦ if sigma i = 0 then P i ∩ Qg i else P i \ Qg i
      let X : Fin 8 → Fin (8 ^ h) → TensorObj K 3 := fun j a ↦
        projected T b label
          (fun i ↦ Finset.univ \ holes' (finProdFinEquiv (m := 8) (n := 8 ^ h) (j, a)) i)
      let Y : Fin 8 → TensorObj K 3 := fun j ↦
        projected T b label (box (enumerate j))
      have hgroup : ∀ j, TensorObj.Restrict (Y j) (TensorObj.bigAdd (X j)) := by
        intro j
        by_cases hkept : enumerate j = (fun _ ↦ 1)
        · have hj : j = kept := enumerate.injective
            (hkept.trans (enumerate.apply_symm_apply _).symm)
          subst j
          have hbox : box (enumerate kept) = (fun i ↦ P i \ Qg i) := by
            rw [hkept]
            rfl
          have hretained := shuffled_broken_projects_to_retained T b label
            (maps g) (basisImage g) (fun i ↦ (system i).move g)
            (hbasis g) (hlabel g) (htensor g) P Q
          have hfirst := first_copy_restrict_bigAdd hc (X kept)
          change TensorObj.Restrict (projected T b label (box (enumerate kept))) _
          rw [hbox]
          exact hretained.trans hfirst
        · apply ih (box (enumerate j))
            (fun a ↦ holes' (finProdFinEquiv (m := 8) (n := 8 ^ h) (j, a)))
          · intro a i
            exact hholes' _ i
          · have hsmall : ∃ i : Fin 3, enumerate j i = 0 := by
              by_contra hnot
              apply hkept
              funext i
              have hi : enumerate j i ≠ 0 := fun hi ↦ hnot ⟨i, hi⟩
              exact Fin.ext (by have hlt := (enumerate j i).isLt; omega)
            obtain ⟨i, hi⟩ := hsmall
            have hle : ∀ k, (box (enumerate j) k).card ≤ (P k).card := by
              intro k
              dsimp [box]
              split
              · exact Finset.card_le_card Finset.inter_subset_left
              · exact Finset.card_le_card Finset.sdiff_subset
            have hshrink : d * (box (enumerate j) i).card ≤ (P i).card := by
              change d * (if enumerate j i = 0 then P i ∩ Qg i else P i \ Qg i).card ≤ _
              rw [if_pos hi]
              exact hole_intersection_shrinks d (P i) (Q i)
                ((system i).move g) (hg i) (hholes' _ i)
            exact product_threshold_descends d h _ _ hvolume
              (product_shrink_of_one_coordinate d _ _ hle i hshrink)
      have hfold := eight_box_projection_restrict T b label P Qg enumerate
      have hgrouped := mme_bigAdd_fin_mul_grouped_restrict X Y hgroup
      have hfamily :
          (fun r : Fin (8 * 8 ^ h) ↦
            X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2) =
          (fun a : Fin (8 * 8 ^ h) ↦
            projected T b label (fun i ↦ Finset.univ \ holes' a i)) := by
        funext r
        have hindex :
            finProdFinEquiv (m := 8) (n := 8 ^ h)
              ((finProdFinEquiv.symm r).1, (finProdFinEquiv.symm r).2) = r :=
          Equiv.apply_symm_apply finProdFinEquiv r
        exact congrArg
          (fun a ↦ projected T b label (fun i ↦ Finset.univ \ holes' a i)) hindex
      have hsource := congrArg TensorObj.bigAdd hfamily
      have hcombined := hfold.trans hgrouped
      have hfinal : TensorObj.Restrict (projected T b label P)
          (TensorObj.bigAdd (fun a : Fin (8 * 8 ^ h) ↦
            projected T b label (fun i ↦ Finset.univ \ holes' a i))) :=
        (congrArg (TensorObj.Restrict (projected T b label P)) hsource).mp hcombined
      have hfull :
          TensorObj.bigAdd (fun a : Fin (8 * 8 ^ h) ↦
            projected T b label (fun i ↦ Finset.univ \ holes' a i)) =
          TensorObj.bigAdd (fun a : Fin (8 ^ (h + 1)) ↦
            projected T b label (fun i ↦ Finset.univ \ holes a i)) :=
        bigAdd_cast_eq hsize
          (fun a ↦ projected T b label (fun i ↦ Finset.univ \ holes a i))
      exact (congrArg (TensorObj.Restrict (projected T b label P)) hfull).mp hfinal
