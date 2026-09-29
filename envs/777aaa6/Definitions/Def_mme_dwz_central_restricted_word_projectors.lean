-- Prove2me | Definitions.Def_mme_dwz_central_restricted_word_projectors
-- name    : mme_dwz_central_restricted_word_projectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T05:50:47.643829+00:00
-- url     : https://prove2.me/theorems/dad58669-fad4-4b9f-aa79-8146fb281ec5
-- title:
--   Literal prescribed-word projectors for the central 022 and 202 tensor powers
-- statement:
--   Let \(\mathcal W\) be the prescribed family of central channel words and let \(D=|\mathcal W|\). The interface embeds each named word by its literal base-\((q^2+2)\) coordinate and defines modewise coordinate projectors from the flattened 022 and 202 tensor powers onto \(\langle 1,1,D\rangle\) and \(\langle D,1,1\rangle\), respectively.\n\nThe projectors preserve exactly the embedded coordinates, annihilate every coordinate outside their image, and send the complete flattened matrix-multiplication tensors to the stated target tensors. They also normalize the two formal \(1^m\)-dimensional modes to their unique coordinates. Thus the retained coordinates remain tied to prescribed CW channel words rather than to an arbitrary \(D\)-dimensional subspace.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_central_power_word_coordinates

open PiTensorProduct BigOperators

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false

instance centralRestricted022WordFinite (q m L G : ℕ) :
    Finite (CentralRestricted022Word q m L G) := by
  unfold CentralRestricted022Word CentralSplitPattern
  infer_instance

noncomputable instance centralRestricted022WordFintype (q m L G : ℕ) :
    Fintype (CentralRestricted022Word q m L G) :=
  Fintype.ofFinite _

private def fine022ChannelClass {q : ℕ} : Fine022Channel q → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private theorem fine022ChannelClass_encode
    {q m L G : ℕ} (w : CentralRestricted022Word q m L G)
    (r : Fin m) :
    fine022ChannelClass (encodeCentralRestricted022Word w r) = w.1.1 r := by
  by_cases h0 : w.1.1 r = (0 : Fin 3)
  · simp [encodeCentralRestricted022Word, fine022ChannelClass, h0]
  by_cases h1 : w.1.1 r = (1 : Fin 3)
  · simp [encodeCentralRestricted022Word, fine022ChannelClass, h1]
  have h2 : w.1.1 r = (2 : Fin 3) := by
    apply Fin.ext
    omega
  simp [encodeCentralRestricted022Word, fine022ChannelClass, h2]

private theorem encodeCentralRestricted022Word_at_middle
    {q m L G : ℕ} (p : CentralSplitPattern m L G)
    (label : {r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q)
    (r : {r : Fin m // p.1 r = (1 : Fin 3)}) :
    encodeCentralRestricted022Word ⟨p, label⟩ r.1 =
      Sum.inr (Sum.inl (label r)) := by
  simp [encodeCentralRestricted022Word, r.2]

theorem encodeCentralRestricted022Word_injective {q m L G : ℕ} :
    Function.Injective
      (encodeCentralRestricted022Word :
        CentralRestricted022Word q m L G →
          (Fin m → Fine022Channel q)) := by
  intro w v h
  have hp : w.1 = v.1 := by
    apply Subtype.ext
    funext r
    rw [← fine022ChannelClass_encode w r,
      ← fine022ChannelClass_encode v r, h]
  cases w with
  | mk wp wl =>
    cases v with
    | mk vp vl =>
      dsimp only at hp
      subst vp
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext r
        have hr := congrFun h r.1
        rw [encodeCentralRestricted022Word_at_middle wp wl r,
          encodeCentralRestricted022Word_at_middle wp vl r] at hr
        exact Sum.inl.inj (Sum.inr.inj hr)

noncomputable def centralRestrictedWordCoordinate {q m L G : ℕ}
    (w : CentralRestricted022Word q m L G) :
    Fin ((q ^ 2 + 2) ^ m) :=
  fineChannelWordIndex q m (encodeCentralRestricted022Word w)

theorem centralRestrictedWordCoordinate_injective {q m L G : ℕ} :
    Function.Injective
      (centralRestrictedWordCoordinate :
        CentralRestricted022Word q m L G →
          Fin ((q ^ 2 + 2) ^ m)) :=
  (fineChannelWordIndex q m).injective.comp
    encodeCentralRestricted022Word_injective

noncomputable def centralRestrictedWordEquivFin (q m L G : ℕ) :
    CentralRestricted022Word q m L G ≃
      Fin (Nat.card (CentralRestricted022Word q m L G)) :=
  (Fintype.equivFin _).trans (finCongr Nat.card_eq_fintype_card.symm)

/-- The literal injection of prescribed words into the full collapsed MM
coordinate set. -/
noncomputable def centralRestrictedWordEmbedding (q m L G : ℕ) :
    Fin (Nat.card (CentralRestricted022Word q m L G)) ↪
      Fin ((q ^ 2 + 2) ^ m) where
  toFun i := centralRestrictedWordCoordinate
    ((centralRestrictedWordEquivFin q m L G).symm i)
  inj' := by
    intro i j h
    apply (centralRestrictedWordEquivFin q m L G).symm.injective
    exact centralRestrictedWordCoordinate_injective h

theorem centralRestrictedWordEmbedding_word
    {q m L G : ℕ} (w : CentralRestricted022Word q m L G) :
    centralRestrictedWordEmbedding q m L G
        (centralRestrictedWordEquivFin q m L G w) =
      centralRestrictedWordCoordinate w := by
  simp [centralRestrictedWordEmbedding]

/-! ## Coordinate projectors after little-endian power flattening -/

/-- Simultaneously normalize the one-point modes and retain only the
coordinates in `e` for a flattened 022 tensor. -/
noncomputable def central022RestrictedProjector
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) :
    ∀ s : Fin 3,
      (MMObj K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m)).V s →ₗ[K]
        (MMObj K 1 1 D).V s
  | ⟨0, _⟩ =>
      LinearMap.funLeft K K
        (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex m, unitWordIndex m))
  | ⟨1, _⟩ =>
      LinearMap.funLeft K K
        (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2))
  | ⟨2, _⟩ =>
      LinearMap.funLeft K K
        (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m))

/-- The corresponding normalized coordinate projector for the 202 rotation. -/
noncomputable def central202RestrictedProjector
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) :
    ∀ s : Fin 3,
      (MMObj K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m)).V s →ₗ[K]
        (MMObj K D 1 1).V s
  | ⟨0, _⟩ =>
      LinearMap.funLeft K K
        (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m))
  | ⟨1, _⟩ =>
      LinearMap.funLeft K K
        (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex m, unitWordIndex m))
  | ⟨2, _⟩ =>
      LinearMap.funLeft K K
        (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2))

noncomputable def restricted022TargetMMVec
    (K : Type u) [Field K] (D : ℕ) (k : Fin D) :
    ∀ s : Fin 3, (MMObj K 1 1 D).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin D → K)
  | ⟨2, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin D × Fin 1 → K)

noncomputable def restricted202TargetMMVec
    (K : Type u) [Field K] (D : ℕ) (k : Fin D) :
    ∀ s : Fin 3, (MMObj K D 1 1).V s
  | ⟨0, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin D × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin D → K)

private theorem funLeft_single_of_injective
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (f : B → A) (hf : Function.Injective f) (b : B) :
    LinearMap.funLeft K K f (Pi.single (f b) 1) =
      (Pi.single b 1 : B → K) := by
  classical
  funext x
  simp only [LinearMap.funLeft_apply, Pi.single_apply, hf.eq_iff]

theorem central022RestrictedProjector_selected
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) (k : Fin D)
    (s : Fin 3) :
    central022RestrictedProjector (K := K) e s
        (central022FlatMMVec K q m (e k) s) =
      restricted022TargetMMVec K D k s := by
  fin_cases s
  all_goals simp only [central022RestrictedProjector,
    central022FlatMMVec, restricted022TargetMMVec]
  · exact funLeft_single_of_injective K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex m, unitWordIndex m))
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      ((0 : Fin 1), (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact e.injective (congrArg Prod.snd h))
      ((0 : Fin 1), k)
  · exact funLeft_single_of_injective K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m))
      (by
        intro a b h
        apply Prod.ext
        · exact e.injective (congrArg Prod.fst h)
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))

theorem central202RestrictedProjector_selected
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) (k : Fin D)
    (s : Fin 3) :
    central202RestrictedProjector (K := K) e s
        (central202FlatMMVec K q m (e k) s) =
      restricted202TargetMMVec K D k s := by
  fin_cases s
  all_goals simp only [central202RestrictedProjector,
    central202FlatMMVec, restricted202TargetMMVec]
  · exact funLeft_single_of_injective K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m))
      (by
        intro a b h
        apply Prod.ext
        · exact e.injective (congrArg Prod.fst h)
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex m, unitWordIndex m))
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      ((0 : Fin 1), (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact e.injective (congrArg Prod.snd h))
      ((0 : Fin 1), k)

/-! ## Complete tensor image of the projectors -/

noncomputable instance unitPowerUnique (m : ℕ) : Unique (Fin (1 ^ m)) where
  default := unitWordIndex m
  uniq x := by
    apply Fin.ext
    have hx : x.val < 1 := by simpa only [one_pow] using x.isLt
    have hu : (unitWordIndex m).val < 1 := by
      simpa only [one_pow] using (unitWordIndex m).isLt
    omega

noncomputable def central022RawPure
    (K : Type u) [Field K] (q m : ℕ)
    (k : Fin ((q ^ 2 + 2) ^ m)) :
    PiTensorProduct K
      (MMSpace K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m)) :=
  tprod K (central022FlatMMVec K q m k)

noncomputable def central202RawPure
    (K : Type u) [Field K] (q m : ℕ)
    (k : Fin ((q ^ 2 + 2) ^ m)) :
    PiTensorProduct K
      (MMSpace K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m)) :=
  tprod K (central202FlatMMVec K q m k)

noncomputable def restricted022TargetPure
    (K : Type u) [Field K] (D : ℕ) (k : Fin D) :
    PiTensorProduct K (MMSpace K 1 1 D) :=
  tprod K (restricted022TargetMMVec K D k)

noncomputable def restricted202TargetPure
    (K : Type u) [Field K] (D : ℕ) (k : Fin D) :
    PiTensorProduct K (MMSpace K D 1 1) :=
  tprod K (restricted202TargetMMVec K D k)

theorem central022RawTensor_eq_sum
    (K : Type u) [Field K] (q m : ℕ) :
    (MMObj K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m)).t =
      ∑ k : Fin ((q ^ 2 + 2) ^ m), central022RawPure K q m k := by
  change MMTensor K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m) = _
  simp only [MMTensor, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem central202RawTensor_eq_sum
    (K : Type u) [Field K] (q m : ℕ) :
    (MMObj K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m)).t =
      ∑ k : Fin ((q ^ 2 + 2) ^ m), central202RawPure K q m k := by
  change MMTensor K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m) = _
  simp only [MMTensor, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem restricted022TargetTensor_eq_sum
    (K : Type u) [Field K] (D : ℕ) :
    (MMObj K 1 1 D).t =
      ∑ k : Fin D, restricted022TargetPure K D k := by
  change MMTensor K 1 1 D = _
  simp only [MMTensor, Fin.sum_univ_one]
  rfl

theorem restricted202TargetTensor_eq_sum
    (K : Type u) [Field K] (D : ℕ) :
    (MMObj K D 1 1).t =
      ∑ k : Fin D, restricted202TargetPure K D k := by
  change MMTensor K D 1 1 = _
  simp only [MMTensor, Fin.sum_univ_one]
  rfl

theorem central022RestrictedProjector_map_selected
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) (k : Fin D) :
    PiTensorProduct.map (central022RestrictedProjector (K := K) e)
        (central022RawPure K q m (e k)) =
      restricted022TargetPure K D k := by
  unfold central022RawPure restricted022TargetPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  exact central022RestrictedProjector_selected e k s

theorem central202RestrictedProjector_map_selected
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) (k : Fin D) :
    PiTensorProduct.map (central202RestrictedProjector (K := K) e)
        (central202RawPure K q m (e k)) =
      restricted202TargetPure K D k := by
  unfold central202RawPure restricted202TargetPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  exact central202RestrictedProjector_selected e k s

private theorem funLeft_single_outside
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] (f : B → A) (a : A)
    (h : ∀ b, f b ≠ a) :
    LinearMap.funLeft K K f (Pi.single a 1) = (0 : B → K) := by
  funext b
  simp [LinearMap.funLeft_apply, Pi.single_apply, h b]

theorem central022RestrictedProjector_map_outside
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m))
    (k' : Fin ((q ^ 2 + 2) ^ m))
    (hout : ∀ k : Fin D, e k ≠ k') :
    PiTensorProduct.map (central022RestrictedProjector (K := K) e)
        (central022RawPure K q m k') = 0 := by
  unfold central022RawPure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
  change (LinearMap.funLeft K K
      (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2)))
      (Pi.single (unitWordIndex m, k') 1) = 0
  apply funLeft_single_outside
  intro ab h
  exact hout ab.2 (congrArg Prod.snd h)

theorem central202RestrictedProjector_map_outside
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m))
    (k' : Fin ((q ^ 2 + 2) ^ m))
    (hout : ∀ k : Fin D, e k ≠ k') :
    PiTensorProduct.map (central202RestrictedProjector (K := K) e)
        (central202RawPure K q m k') = 0 := by
  unfold central202RawPure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  change (LinearMap.funLeft K K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m)))
      (Pi.single (k', unitWordIndex m) 1) = 0
  apply funLeft_single_outside
  intro ab h
  exact hout ab.1 (congrArg Prod.fst h)

theorem central022RestrictedProjector_maps_tensor
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) :
    PiTensorProduct.map (central022RestrictedProjector (K := K) e)
        (MMObj K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m)).t =
      (MMObj K 1 1 D).t := by
  rw [central022RawTensor_eq_sum, restricted022TargetTensor_eq_sum]
  refine (map_sum
    (PiTensorProduct.map (central022RestrictedProjector (K := K) e))
    (fun k : Fin ((q ^ 2 + 2) ^ m) ↦ central022RawPure K q m k)
    Finset.univ).trans ?_
  let range : Finset (Fin ((q ^ 2 + 2) ^ m)) := Finset.univ.image e
  calc
    (∑ k' : Fin ((q ^ 2 + 2) ^ m),
        PiTensorProduct.map (central022RestrictedProjector (K := K) e)
          (central022RawPure K q m k')) =
        ∑ k' ∈ range,
          PiTensorProduct.map (central022RestrictedProjector (K := K) e)
            (central022RawPure K q m k') := by
      symm
      apply Finset.sum_subset
      · simp [range]
      · intro k' _ hk'
        apply central022RestrictedProjector_map_outside
        intro k hek
        apply hk'
        simp [range, ← hek]
    _ = ∑ k : Fin D,
          PiTensorProduct.map (central022RestrictedProjector (K := K) e)
            (central022RawPure K q m (e k)) := by
      simp only [range]
      exact Finset.sum_image e.injective.injOn
    _ = ∑ k : Fin D, restricted022TargetPure K D k := by
      apply Finset.sum_congr rfl
      intro k _
      exact central022RestrictedProjector_map_selected e k

theorem central202RestrictedProjector_maps_tensor
    {K : Type u} [Field K] {q m D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m)) :
    PiTensorProduct.map (central202RestrictedProjector (K := K) e)
        (MMObj K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m)).t =
      (MMObj K D 1 1).t := by
  rw [central202RawTensor_eq_sum, restricted202TargetTensor_eq_sum]
  refine (map_sum
    (PiTensorProduct.map (central202RestrictedProjector (K := K) e))
    (fun k : Fin ((q ^ 2 + 2) ^ m) ↦ central202RawPure K q m k)
    Finset.univ).trans ?_
  let range : Finset (Fin ((q ^ 2 + 2) ^ m)) := Finset.univ.image e
  calc
    (∑ k' : Fin ((q ^ 2 + 2) ^ m),
        PiTensorProduct.map (central202RestrictedProjector (K := K) e)
          (central202RawPure K q m k')) =
        ∑ k' ∈ range,
          PiTensorProduct.map (central202RestrictedProjector (K := K) e)
            (central202RawPure K q m k') := by
      symm
      apply Finset.sum_subset
      · simp [range]
      · intro k' _ hk'
        apply central202RestrictedProjector_map_outside
        intro k hek
        apply hk'
        simp [range, ← hek]
    _ = ∑ k : Fin D,
          PiTensorProduct.map (central202RestrictedProjector (K := K) e)
            (central202RawPure K q m (e k)) := by
      simp only [range]
      exact Finset.sum_image e.injective.injOn
    _ = ∑ k : Fin D, restricted202TargetPure K D k := by
      apply Finset.sum_congr rfl
      intro k _
      exact central202RestrictedProjector_map_selected e k

end MME.DWZFineChannel


