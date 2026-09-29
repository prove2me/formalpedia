-- Prove2me | solution 1 for mme_bigAdd_identical_MM_to_flat_MM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:53:17.602223+00:00
-- url     : https://prove2.me/submissions/7c8258ae-715e-4272-9bd7-efc7f13d8288

import Theorems.Thm_mme_bigAdd_identical_MM_to_flat_MM

/-! # `Sol_mme_bigAdd_identical_MM_to_flat_MM`

`MMObj K (k * a) b c` restricts from `bigAdd (fun _ : Fin k => MMObj K a b c)`.

Proof outline (by induction on `k`):
* `k = 0` — `bigAdd = zeroObj`, `MMObj K 0 b c` has zero tensor (empty `Fin 0` sum).
* `k = 1` — `bigAdd = MMObj K a b c`, target is `MMObj K (1 * a) b c`; rewrite
  `1 * a = a` and use the identity.
* `k + 2` — `bigAdd = add (MMObj K a b c) (bigAdd_{k+1})`. By induction we have
  `Restrict (MMObj K ((k+1)*a) b c) bigAdd_{k+1}`. A "merge" lemma gives
  `Restrict (MMObj K (a + (k+1)*a) b c) (add (MMObj K a b c) (MMObj K ((k+1)*a) b c))`.
  Compose via functoriality of `add` and transitivity, then use `a + (k+1)*a = (k+2)*a`. -/

open MME PiTensorProduct BigOperators

universe u

set_option maxHeartbeats 200000

namespace MMEBigAddIdenticalMMToFlatMM

variable {K : Type u} [Field K]

/-! ## Helper: distribute a LinearMap over a triple-nested Finset sum. -/

private lemma linMap_triple_sum {K : Type u} [Field K] {α β γ M N : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) (g : α → β → γ → M) :
    f (∑ i, ∑ j, ∑ k, g i j k) = ∑ i, ∑ j, ∑ k, f (g i j k) := by
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl; intros i _
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl; intros j _
  rw [_root_.map_sum]

/-! ## Restrict preorder helpers. -/

private theorem restrict_refl {d : ℕ} (X : TensorObj K d) :
    TensorObj.Restrict X X :=
  ⟨fun _ => LinearMap.id, by rw [PiTensorProduct.map_id]; rfl⟩

private theorem restrict_trans {d : ℕ} {X Y Z : TensorObj K d}
    (hXY : TensorObj.Restrict X Y) (hYZ : TensorObj.Restrict Y Z) :
    TensorObj.Restrict X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  refine ⟨fun i => f i ∘ₗ g i, ?_⟩
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hg, hf]

/-! ## Functoriality of `add` under `Restrict`. -/

/-- If `Restrict X₁ Y₁` and `Restrict X₂ Y₂`, then `Restrict (add X₁ X₂) (add Y₁ Y₂)`. -/
private theorem restrict_add_congr {d : ℕ} {X₁ Y₁ X₂ Y₂ : TensorObj K d}
    (h₁ : TensorObj.Restrict X₁ Y₁) (h₂ : TensorObj.Restrict X₂ Y₂) :
    TensorObj.Restrict (TensorObj.add X₁ X₂) (TensorObj.add Y₁ Y₂) := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  refine ⟨fun i => (f₁ i).prodMap (f₂ i), ?_⟩
  -- Need: map (prodMap f₁ f₂) (map inl Y₁.t + map inr Y₂.t) = map inl X₁.t + map inr X₂.t
  show PiTensorProduct.map (fun i => (f₁ i).prodMap (f₂ i))
      ((PiTensorProduct.map (fun i => LinearMap.inl K (Y₁.V i) (Y₂.V i)) Y₁.t) +
       (PiTensorProduct.map (fun i => LinearMap.inr K (Y₁.V i) (Y₂.V i)) Y₂.t)) =
    (PiTensorProduct.map (fun i => LinearMap.inl K (X₁.V i) (X₂.V i)) X₁.t) +
    (PiTensorProduct.map (fun i => LinearMap.inr K (X₁.V i) (X₂.V i)) X₂.t)
  rw [map_add]
  congr 1
  · rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have heq :
        (fun i => (f₁ i).prodMap (f₂ i) ∘ₗ LinearMap.inl K (Y₁.V i) (Y₂.V i)) =
        fun i => LinearMap.inl K (X₁.V i) (X₂.V i) ∘ₗ f₁ i := by
      funext i
      apply LinearMap.ext
      intro y
      ext
      · simp [LinearMap.prodMap_apply]
      · simp [LinearMap.prodMap_apply]
    rw [heq, PiTensorProduct.map_comp, LinearMap.comp_apply, hf₁]
  · rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have heq :
        (fun i => (f₁ i).prodMap (f₂ i) ∘ₗ LinearMap.inr K (Y₁.V i) (Y₂.V i)) =
        fun i => LinearMap.inr K (X₁.V i) (X₂.V i) ∘ₗ f₂ i := by
      funext i
      apply LinearMap.ext
      intro y
      ext
      · simp [LinearMap.prodMap_apply]
      · simp [LinearMap.prodMap_apply]
    rw [heq, PiTensorProduct.map_comp, LinearMap.comp_apply, hf₂]

/-! ## Local copy of `MMPure` and `MMObj` unfolding. -/

private noncomputable def MMPure (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

private theorem MMObj_t_eq (n m p : ℕ) :
    (MMObj K n m p).t = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k := rfl

/-- The tensor of `add X Y`, stated generically (proved by `rfl` once so the giant
unfolded form never has to be `whnf`-checked at every use site). -/
private theorem add_t_eq {d : ℕ} (X Y : TensorObj K d) :
    (TensorObj.add X Y).t =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t := rfl

/-! ## Zero case: `MMObj K 0 b c` is restricted from `zeroObj`. -/

private theorem MMObj_zero_restrict_zeroObj (b c : ℕ) :
    TensorObj.Restrict (MMObj K 0 b c) (TensorObj.zeroObj : TensorObj K 3) := by
  refine ⟨fun i => (0 : PUnit →ₗ[K] (MMObj K 0 b c).V i), ?_⟩
  show PiTensorProduct.map (fun i => (0 : PUnit →ₗ[K] (MMObj K 0 b c).V i))
      (0 : PiTensorProduct K (fun _ : Fin 3 => PUnit)) = (MMObj K 0 b c).t
  rw [LinearMap.map_zero]
  -- `(MMObj K 0 b c).t = ∑ i : Fin 0, ...` = 0.
  show (0 : PiTensorProduct K (MMSpace K 0 b c)) = (MMObj K 0 b c).t
  rw [MMObj_t_eq, Fin.sum_univ_zero]

/-! ## One case: `MMObj K (1 * a) b c` restricts from `MMObj K a b c`. -/

private theorem MMObj_one_mul_restrict (a b c : ℕ) :
    TensorObj.Restrict (MMObj K (1 * a) b c) (MMObj K a b c) := by
  -- The cast equiv `Fin a ≃ Fin (1*a)` via `1 * a = a`.
  let e : Fin a ≃ Fin (1 * a) := (Fin.castOrderIso (Nat.one_mul a).symm).toEquiv
  let f₀ : (MMObj K a b c).V 0 →ₗ[K] (MMObj K (1*a) b c).V 0 :=
    LinearMap.funLeft K K (fun ab : Fin (1*a) × Fin b => (e.symm ab.1, ab.2))
  let f₁ : (MMObj K a b c).V 1 →ₗ[K] (MMObj K (1*a) b c).V 1 := LinearMap.id
  let f₂ : (MMObj K a b c).V 2 →ₗ[K] (MMObj K (1*a) b c).V 2 :=
    LinearMap.funLeft K K (fun ab : Fin c × Fin (1*a) => (ab.1, e.symm ab.2))
  let hf : ∀ s : Fin 3, (MMObj K a b c).V s →ₗ[K] (MMObj K (1*a) b c).V s :=
    fun s => Fin.cases f₀ (fun s => Fin.cases f₁ (fun s => Fin.cases f₂
      (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨hf, ?_⟩
  have key : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      PiTensorProduct.map hf (MMPure K a b c i j k) =
      MMPure K (1*a) b c (e i) j k := by
    intro i j k
    simp only [MMPure, hf, f₀, f₁, f₂]
    erw [PiTensorProduct.map_tprod]
    congr 1; funext s
    match s with
    | ⟨0, _⟩ =>
      change (LinearMap.funLeft K K (fun ab : Fin (1*a) × Fin b => (e.symm ab.1, ab.2)))
        (Pi.single (i, j) 1) = Pi.single (e i, j) 1
      funext ⟨x, y⟩
      rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, e.symm_apply_eq]
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ =>
      change (LinearMap.funLeft K K (fun ab : Fin c × Fin (1*a) => (ab.1, e.symm ab.2)))
        (Pi.single (k, i) 1) = Pi.single (k, e i) 1
      funext ⟨x, y⟩
      rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, e.symm_apply_eq]
  -- Compute the map of the whole tensor.
  show PiTensorProduct.map hf (MMObj K a b c).t = (MMObj K (1*a) b c).t
  rw [MMObj_t_eq, MMObj_t_eq]
  calc PiTensorProduct.map hf
        (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c, MMPure K a b c i j k)
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
          PiTensorProduct.map hf (MMPure K a b c i j k) := linMap_triple_sum _ _
    _ = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
          MMPure K (1*a) b c (e i) j k := by
        apply Finset.sum_congr rfl; intros i _
        apply Finset.sum_congr rfl; intros j _
        apply Finset.sum_congr rfl; intros k _
        exact key i j k
    _ = ∑ i' : Fin (1*a), ∑ j : Fin b, ∑ k : Fin c, MMPure K (1*a) b c i' j k :=
        Equiv.sum_comp e (fun i' => ∑ j : Fin b, ∑ k : Fin c, MMPure K (1*a) b c i' j k)

/-! ## The merge lemma:
    `MMObj K (a + a') b c` is restricted from `add (MMObj K a b c) (MMObj K a' b c)`. -/

/-- Mode 0 merge: `(u, v) ↦ Fin.addCases (...u...) (...v...)`. -/
private noncomputable def mergeMode0 (a a' b : ℕ) :
    ((Fin a × Fin b → K) × (Fin a' × Fin b → K)) →ₗ[K] (Fin (a + a') × Fin b → K) where
  toFun uv := fun ij => Fin.addCases (fun i' => uv.1 (i', ij.2)) (fun i' => uv.2 (i', ij.2)) ij.1
  map_add' x y := by
    funext ⟨i, j⟩
    refine Fin.addCases ?_ ?_ i <;> intro i' <;> simp [Fin.addCases_left, Fin.addCases_right]
  map_smul' s x := by
    funext ⟨i, j⟩
    refine Fin.addCases ?_ ?_ i <;> intro i' <;> simp [Fin.addCases_left, Fin.addCases_right]

/-- Mode 1 merge: `(u, v) ↦ u + v`. -/
private noncomputable def mergeMode1 (b c : ℕ) :
    ((Fin b × Fin c → K) × (Fin b × Fin c → K)) →ₗ[K] (Fin b × Fin c → K) where
  toFun uv := uv.1 + uv.2
  map_add' x y := by funext ij; simp; ring
  map_smul' s x := by funext ij; simp [mul_add]

/-- Mode 2 merge: split on the second argument. -/
private noncomputable def mergeMode2 (a a' c : ℕ) :
    ((Fin c × Fin a → K) × (Fin c × Fin a' → K)) →ₗ[K] (Fin c × Fin (a + a') → K) where
  toFun uv := fun ij => Fin.addCases (fun i' => uv.1 (ij.1, i')) (fun i' => uv.2 (ij.1, i')) ij.2
  map_add' x y := by
    funext ⟨i, j⟩
    refine Fin.addCases ?_ ?_ j <;> intro j' <;> simp [Fin.addCases_left, Fin.addCases_right]
  map_smul' c x := by
    funext ⟨i, j⟩
    refine Fin.addCases ?_ ?_ j <;> intro j' <;> simp [Fin.addCases_left, Fin.addCases_right]

/-- The combined merge witness. -/
private noncomputable def mergeMaps (a a' b c : ℕ) :
    ∀ s : Fin 3, (TensorObj.add (MMObj K a b c) (MMObj K a' b c)).V s →ₗ[K]
      (MMObj K (a + a') b c).V s := fun s =>
  match s with
  | ⟨0, _⟩ => mergeMode0 (K := K) a a' b
  | ⟨1, _⟩ => mergeMode1 (K := K) b c
  | ⟨2, _⟩ => mergeMode2 (K := K) a a' c

/-! ## Pointwise evaluations of `mergeMaps` on basis pairs.

We compute `mergeMaps s ((u, v))` where one of `u, v` is `Pi.single` and the other is `0`. -/

private lemma mergeMaps_inl_apply_0 (a a' b : ℕ) (i : Fin a) (j : Fin b) :
    mergeMode0 (K := K) a a' b ((Pi.single (i, j) 1 : Fin a × Fin b → K), 0) =
      (Pi.single (Fin.castAdd a' i, j) 1 : Fin (a + a') × Fin b → K) := by
  funext ⟨x, y⟩
  simp only [mergeMode0, LinearMap.coe_mk, AddHom.coe_mk]
  refine Fin.addCases ?_ ?_ x
  · intro x'
    rw [Fin.addCases_left]
    by_cases hx : x' = i ∧ y = j
    · obtain ⟨hx1, hx2⟩ := hx
      subst hx1 hx2
      simp [Pi.single_eq_same]
    · rw [not_and_or] at hx
      rw [Pi.single_apply]
      split_ifs with h1
      · rw [Prod.mk.injEq] at h1
        rcases hx with hx | hx
        · exact absurd h1.1 hx
        · exact absurd h1.2 hx
      · rw [Pi.single_apply]
        split_ifs with h2
        · rw [Prod.mk.injEq] at h2
          exfalso
          apply h1
          exact Prod.ext (Fin.castAdd_inj.mp h2.1) h2.2
        · rfl
  · intro x'
    rw [Fin.addCases_right]
    have hzero : ((0 : Fin a' × Fin b → K)) (x', y) = (0 : K) := Pi.zero_apply _
    rw [hzero]
    rw [Pi.single_apply]
    split_ifs with h
    · rw [Prod.mk.injEq] at h
      have : (Fin.natAdd a x').val = (Fin.castAdd a' i).val := congrArg Fin.val h.1
      simp [Fin.natAdd, Fin.castAdd] at this
      omega
    · rfl

private lemma mergeMaps_inl_apply_1 (b c : ℕ) (j : Fin b) (k : Fin c) :
    mergeMode1 (K := K) b c ((Pi.single (j, k) 1 : Fin b × Fin c → K), 0) =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) := by
  show (Pi.single (j, k) 1 : Fin b × Fin c → K) + 0 = _
  rw [add_zero]

private lemma mergeMaps_inl_apply_2 (a a' c : ℕ) (k : Fin c) (i : Fin a) :
    mergeMode2 (K := K) a a' c ((Pi.single (k, i) 1 : Fin c × Fin a → K), 0) =
      (Pi.single (k, Fin.castAdd a' i) 1 : Fin c × Fin (a + a') → K) := by
  funext ⟨x, y⟩
  simp only [mergeMode2, LinearMap.coe_mk, AddHom.coe_mk]
  refine Fin.addCases ?_ ?_ y
  · intro y'
    rw [Fin.addCases_left]
    by_cases hy : x = k ∧ y' = i
    · obtain ⟨hy1, hy2⟩ := hy
      subst hy1 hy2
      simp [Pi.single_eq_same]
    · rw [not_and_or] at hy
      rw [Pi.single_apply]
      split_ifs with h1
      · rw [Prod.mk.injEq] at h1
        rcases hy with hy | hy
        · exact absurd h1.1 hy
        · exact absurd h1.2 hy
      · rw [Pi.single_apply]
        split_ifs with h2
        · rw [Prod.mk.injEq] at h2
          exfalso
          apply h1
          exact Prod.ext h2.1 (Fin.castAdd_inj.mp h2.2)
        · rfl
  · intro y'
    rw [Fin.addCases_right]
    have hzero : ((0 : Fin c × Fin a' → K)) (x, y') = (0 : K) := Pi.zero_apply _
    rw [hzero]
    rw [Pi.single_apply]
    split_ifs with h
    · rw [Prod.mk.injEq] at h
      have : (Fin.natAdd a y').val = (Fin.castAdd a' i).val := congrArg Fin.val h.2
      simp [Fin.natAdd, Fin.castAdd] at this
      omega
    · rfl

private lemma mergeMaps_inr_apply_0 (a a' b : ℕ) (i : Fin a') (j : Fin b) :
    mergeMode0 (K := K) a a' b ((0 : Fin a × Fin b → K), Pi.single (i, j) 1) =
      (Pi.single (Fin.natAdd a i, j) 1 : Fin (a + a') × Fin b → K) := by
  funext ⟨x, y⟩
  simp only [mergeMode0, LinearMap.coe_mk, AddHom.coe_mk]
  refine Fin.addCases ?_ ?_ x
  · intro x'
    rw [Fin.addCases_left]
    have hzero : ((0 : Fin a × Fin b → K)) (x', y) = (0 : K) := Pi.zero_apply _
    rw [hzero]
    rw [Pi.single_apply]
    split_ifs with h
    · rw [Prod.mk.injEq] at h
      have : (Fin.castAdd a' x').val = (Fin.natAdd a i).val := congrArg Fin.val h.1
      simp [Fin.castAdd, Fin.natAdd] at this
      omega
    · rfl
  · intro x'
    rw [Fin.addCases_right]
    by_cases hx : x' = i ∧ y = j
    · obtain ⟨hx1, hx2⟩ := hx
      subst hx1 hx2
      simp [Pi.single_eq_same]
    · rw [not_and_or] at hx
      rw [Pi.single_apply]
      split_ifs with h1
      · rw [Prod.mk.injEq] at h1
        rcases hx with hx | hx
        · exact absurd h1.1 hx
        · exact absurd h1.2 hx
      · rw [Pi.single_apply]
        split_ifs with h2
        · rw [Prod.mk.injEq] at h2
          exfalso
          apply h1
          have hv : (Fin.natAdd a x').val = (Fin.natAdd a i).val := congrArg Fin.val h2.1
          simp [Fin.natAdd] at hv
          exact Prod.ext (Fin.ext hv) h2.2
        · rfl

private lemma mergeMaps_inr_apply_1 (b c : ℕ) (j : Fin b) (k : Fin c) :
    mergeMode1 (K := K) b c ((0 : Fin b × Fin c → K), Pi.single (j, k) 1) =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) := by
  show (0 : Fin b × Fin c → K) + (Pi.single (j, k) 1 : Fin b × Fin c → K) = _
  rw [zero_add]

private lemma mergeMaps_inr_apply_2 (a a' c : ℕ) (k : Fin c) (i : Fin a') :
    mergeMode2 (K := K) a a' c ((0 : Fin c × Fin a → K), Pi.single (k, i) 1) =
      (Pi.single (k, Fin.natAdd a i) 1 : Fin c × Fin (a + a') → K) := by
  funext ⟨x, y⟩
  simp only [mergeMode2, LinearMap.coe_mk, AddHom.coe_mk]
  refine Fin.addCases ?_ ?_ y
  · intro y'
    rw [Fin.addCases_left]
    have hzero : ((0 : Fin c × Fin a → K)) (x, y') = (0 : K) := Pi.zero_apply _
    rw [hzero]
    rw [Pi.single_apply]
    split_ifs with h
    · rw [Prod.mk.injEq] at h
      have : (Fin.castAdd a' y').val = (Fin.natAdd a i).val := congrArg Fin.val h.2
      simp [Fin.castAdd, Fin.natAdd] at this
      omega
    · rfl
  · intro y'
    rw [Fin.addCases_right]
    by_cases hy : x = k ∧ y' = i
    · obtain ⟨hy1, hy2⟩ := hy
      subst hy1 hy2
      simp [Pi.single_eq_same]
    · rw [not_and_or] at hy
      rw [Pi.single_apply]
      split_ifs with h1
      · rw [Prod.mk.injEq] at h1
        rcases hy with hy | hy
        · exact absurd h1.1 hy
        · exact absurd h1.2 hy
      · rw [Pi.single_apply]
        split_ifs with h2
        · rw [Prod.mk.injEq] at h2
          exfalso
          apply h1
          have hv : (Fin.natAdd a y').val = (Fin.natAdd a i).val := congrArg Fin.val h2.2
          simp [Fin.natAdd] at hv
          exact Prod.ext h2.1 (Fin.ext hv)
        · rfl

/-! ## Action of `mergeMaps ∘ₗ inl` and `mergeMaps ∘ₗ inr` on `MMPure`. -/

/-- For each mode, `mergeMaps i ∘ₗ inl_i` evaluated on basis of the first MM. -/
private lemma mergeMaps_inl_pre_apply_0 (a a' b c : ℕ) (i : Fin a) (j : Fin b) :
    mergeMaps (K := K) a a' b c ⟨0, by omega⟩
      ((LinearMap.inl K ((MMObj K a b c).V ⟨0, by omega⟩) ((MMObj K a' b c).V ⟨0, by omega⟩))
        (Pi.single (i, j) 1 : Fin a × Fin b → K)) =
      (Pi.single (Fin.castAdd a' i, j) 1 : Fin (a + a') × Fin b → K) := by
  show mergeMode0 (K := K) a a' b ((Pi.single (i, j) 1 : Fin a × Fin b → K), 0) = _
  exact mergeMaps_inl_apply_0 (K := K) a a' b i j

private lemma mergeMaps_inl_pre_apply_1 (a a' b c : ℕ) (j : Fin b) (k : Fin c) :
    mergeMaps (K := K) a a' b c ⟨1, by omega⟩
      ((LinearMap.inl K ((MMObj K a b c).V ⟨1, by omega⟩) ((MMObj K a' b c).V ⟨1, by omega⟩))
        (Pi.single (j, k) 1 : Fin b × Fin c → K)) =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) := by
  show mergeMode1 (K := K) b c ((Pi.single (j, k) 1 : Fin b × Fin c → K), 0) = _
  exact mergeMaps_inl_apply_1 (K := K) b c j k

private lemma mergeMaps_inl_pre_apply_2 (a a' b c : ℕ) (k : Fin c) (i : Fin a) :
    mergeMaps (K := K) a a' b c ⟨2, by omega⟩
      ((LinearMap.inl K ((MMObj K a b c).V ⟨2, by omega⟩) ((MMObj K a' b c).V ⟨2, by omega⟩))
        (Pi.single (k, i) 1 : Fin c × Fin a → K)) =
      (Pi.single (k, Fin.castAdd a' i) 1 : Fin c × Fin (a + a') → K) := by
  show mergeMode2 (K := K) a a' c ((Pi.single (k, i) 1 : Fin c × Fin a → K), 0) = _
  exact mergeMaps_inl_apply_2 (K := K) a a' c k i

private lemma mergeMaps_inr_pre_apply_0 (a a' b c : ℕ) (i : Fin a') (j : Fin b) :
    mergeMaps (K := K) a a' b c ⟨0, by omega⟩
      ((LinearMap.inr K ((MMObj K a b c).V ⟨0, by omega⟩) ((MMObj K a' b c).V ⟨0, by omega⟩))
        (Pi.single (i, j) 1 : Fin a' × Fin b → K)) =
      (Pi.single (Fin.natAdd a i, j) 1 : Fin (a + a') × Fin b → K) := by
  show mergeMode0 (K := K) a a' b ((0 : Fin a × Fin b → K), (Pi.single (i, j) 1 : Fin a' × Fin b → K)) = _
  exact mergeMaps_inr_apply_0 (K := K) a a' b i j

private lemma mergeMaps_inr_pre_apply_1 (a a' b c : ℕ) (j : Fin b) (k : Fin c) :
    mergeMaps (K := K) a a' b c ⟨1, by omega⟩
      ((LinearMap.inr K ((MMObj K a b c).V ⟨1, by omega⟩) ((MMObj K a' b c).V ⟨1, by omega⟩))
        (Pi.single (j, k) 1 : Fin b × Fin c → K)) =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) := by
  show mergeMode1 (K := K) b c ((0 : Fin b × Fin c → K), (Pi.single (j, k) 1 : Fin b × Fin c → K)) = _
  exact mergeMaps_inr_apply_1 (K := K) b c j k

private lemma mergeMaps_inr_pre_apply_2 (a a' b c : ℕ) (k : Fin c) (i : Fin a') :
    mergeMaps (K := K) a a' b c ⟨2, by omega⟩
      ((LinearMap.inr K ((MMObj K a b c).V ⟨2, by omega⟩) ((MMObj K a' b c).V ⟨2, by omega⟩))
        (Pi.single (k, i) 1 : Fin c × Fin a' → K)) =
      (Pi.single (k, Fin.natAdd a i) 1 : Fin c × Fin (a + a') → K) := by
  show mergeMode2 (K := K) a a' c ((0 : Fin c × Fin a → K), (Pi.single (k, i) 1 : Fin c × Fin a' → K)) = _
  exact mergeMaps_inr_apply_2 (K := K) a a' c k i

/-- `mergeMaps ∘ map(inl)` applied to `MMPure K a b c i j k` = `MMPure K (a+a') b c (castAdd i) j k`. -/
private lemma mergeMaps_inl_MMPure (a a' b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct.map (mergeMaps (K := K) a a' b c)
      (PiTensorProduct.map
        (fun s => LinearMap.inl K ((MMObj K a b c).V s) ((MMObj K a' b c).V s))
        (MMPure K a b c i j k)) =
      MMPure K (a + a') b c (Fin.castAdd a' i) j k := by
  -- Rewrite the `inl` map family to the *syntactic* `MMSpace` form so the inner
  -- `map_tprod` fires with a cheap `rw` (no whnf storm); the outer `map mergeMaps`
  -- then sits directly on a `tprod`, so its `erw` is trivial.
  show PiTensorProduct.map (mergeMaps (K := K) a a' b c)
      (PiTensorProduct.map
        (fun s => LinearMap.inl K (MMSpace K a b c s) (MMSpace K a' b c s))
        (MMPure K a b c i j k)) = _
  unfold MMPure
  rw [PiTensorProduct.map_tprod]
  erw [PiTensorProduct.map_tprod]
  congr 1; funext s
  match s with
  | ⟨0, _⟩ => exact mergeMaps_inl_pre_apply_0 (K := K) a a' b c i j
  | ⟨1, _⟩ => exact mergeMaps_inl_pre_apply_1 (K := K) a a' b c j k
  | ⟨2, _⟩ => exact mergeMaps_inl_pre_apply_2 (K := K) a a' b c k i

private lemma mergeMaps_inr_MMPure (a a' b c : ℕ) (i : Fin a') (j : Fin b) (k : Fin c) :
    PiTensorProduct.map (mergeMaps (K := K) a a' b c)
      (PiTensorProduct.map
        (fun s => LinearMap.inr K ((MMObj K a b c).V s) ((MMObj K a' b c).V s))
        (MMPure K a' b c i j k)) =
      MMPure K (a + a') b c (Fin.natAdd a i) j k := by
  show PiTensorProduct.map (mergeMaps (K := K) a a' b c)
      (PiTensorProduct.map
        (fun s => LinearMap.inr K (MMSpace K a b c s) (MMSpace K a' b c s))
        (MMPure K a' b c i j k)) = _
  unfold MMPure
  rw [PiTensorProduct.map_tprod]
  erw [PiTensorProduct.map_tprod]
  congr 1; funext s
  match s with
  | ⟨0, _⟩ => exact mergeMaps_inr_pre_apply_0 (K := K) a a' b c i j
  | ⟨1, _⟩ => exact mergeMaps_inr_pre_apply_1 (K := K) a a' b c j k
  | ⟨2, _⟩ => exact mergeMaps_inr_pre_apply_2 (K := K) a a' b c k i

/-- **The merge lemma**: `MMObj K (a + a') b c` is restricted from
`add (MMObj K a b c) (MMObj K a' b c)`. -/
private theorem MMObj_add_restrict (a a' b c : ℕ) :
    TensorObj.Restrict (MMObj K (a + a') b c)
      (TensorObj.add (MMObj K a b c) (MMObj K a' b c)) := by
  refine ⟨mergeMaps (K := K) a a' b c, ?_⟩
  -- `(add ...).t = map inl X.t + map inr Y.t`, then push the outer `map` through `+`.
  rw [add_t_eq]
  -- Bind the two summands so `map_add` applies without re-`whnf`-ing the giant terms.
  set A := PiTensorProduct.map
      (fun i => LinearMap.inl K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)) (MMObj K a b c).t
    with hA
  set B := PiTensorProduct.map
      (fun i => LinearMap.inr K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)) (MMObj K a' b c).t
    with hB
  rw [show (PiTensorProduct.map (mergeMaps (K := K) a a' b c)) (A + B) =
        (PiTensorProduct.map (mergeMaps (K := K) a a' b c)) A +
        (PiTensorProduct.map (mergeMaps (K := K) a a' b c)) B from
      map_add _ _ _, hA, hB]
  -- Compute each summand using MMPure decomposition.
  have h_lhs1 : PiTensorProduct.map (mergeMaps (K := K) a a' b c)
        (PiTensorProduct.map (fun i =>
            LinearMap.inl K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)) (MMObj K a b c).t) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        MMPure K (a + a') b c (Fin.castAdd a' i) j k := by
    rw [MMObj_t_eq]
    calc PiTensorProduct.map (mergeMaps (K := K) a a' b c)
          ((PiTensorProduct.map (fun i =>
              LinearMap.inl K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)))
            (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c, MMPure K a b c i j k))
        = (PiTensorProduct.map (mergeMaps (K := K) a a' b c) ∘ₗ
            PiTensorProduct.map (fun i =>
              LinearMap.inl K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)))
            (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c, MMPure K a b c i j k) := rfl
      _ = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
            (PiTensorProduct.map (mergeMaps (K := K) a a' b c) ∘ₗ
              PiTensorProduct.map (fun s =>
                LinearMap.inl K ((MMObj K a b c).V s) ((MMObj K a' b c).V s)))
              (MMPure K a b c i j k) := by
          exact linMap_triple_sum _ _
      _ = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
            PiTensorProduct.map (mergeMaps (K := K) a a' b c)
              (PiTensorProduct.map (fun s =>
                LinearMap.inl K ((MMObj K a b c).V s) ((MMObj K a' b c).V s))
                (MMPure K a b c i j k)) := by rfl
      _ = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
            MMPure K (a + a') b c (Fin.castAdd a' i) j k := by
          apply Finset.sum_congr rfl; intros i _
          apply Finset.sum_congr rfl; intros j _
          apply Finset.sum_congr rfl; intros k _
          exact mergeMaps_inl_MMPure (K := K) a a' b c i j k
  have h_lhs2 : PiTensorProduct.map (mergeMaps (K := K) a a' b c)
        (PiTensorProduct.map (fun i =>
            LinearMap.inr K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)) (MMObj K a' b c).t) =
      ∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c,
        MMPure K (a + a') b c (Fin.natAdd a i) j k := by
    rw [MMObj_t_eq]
    calc PiTensorProduct.map (mergeMaps (K := K) a a' b c)
          ((PiTensorProduct.map (fun i =>
              LinearMap.inr K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)))
            (∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c, MMPure K a' b c i j k))
        = (PiTensorProduct.map (mergeMaps (K := K) a a' b c) ∘ₗ
            PiTensorProduct.map (fun i =>
              LinearMap.inr K ((MMObj K a b c).V i) ((MMObj K a' b c).V i)))
            (∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c, MMPure K a' b c i j k) := rfl
      _ = ∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c,
            (PiTensorProduct.map (mergeMaps (K := K) a a' b c) ∘ₗ
              PiTensorProduct.map (fun s =>
                LinearMap.inr K ((MMObj K a b c).V s) ((MMObj K a' b c).V s)))
              (MMPure K a' b c i j k) := by
          exact linMap_triple_sum _ _
      _ = ∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c,
            PiTensorProduct.map (mergeMaps (K := K) a a' b c)
              (PiTensorProduct.map (fun s =>
                LinearMap.inr K ((MMObj K a b c).V s) ((MMObj K a' b c).V s))
                (MMPure K a' b c i j k)) := by rfl
      _ = ∑ i : Fin a', ∑ j : Fin b, ∑ k : Fin c,
            MMPure K (a + a') b c (Fin.natAdd a i) j k := by
          apply Finset.sum_congr rfl; intros i _
          apply Finset.sum_congr rfl; intros j _
          apply Finset.sum_congr rfl; intros k _
          exact mergeMaps_inr_MMPure (K := K) a a' b c i j k
  rw [h_lhs1, h_lhs2]
  -- Show: (∑_{castAdd} ...) + (∑_{natAdd} ...) = ∑_{Fin (a+a')} ...
  rw [MMObj_t_eq]
  rw [Fin.sum_univ_add (fun i => ∑ j : Fin b, ∑ k : Fin c, MMPure K (a + a') b c i j k)]
  rfl

end MMEBigAddIdenticalMMToFlatMM

/-! ## Main proof: induction on `k`. -/

open MMEBigAddIdenticalMMToFlatMM

/-- The main induction. -/
private theorem mme_bigAdd_identical_MM_to_flat_MM_aux
    {K : Type u} [Field K] (a b c : ℕ) :
    ∀ k : ℕ,
      TensorObj.Restrict
        (MMObj K (k * a) b c)
        (TensorObj.bigAdd (fun _ : Fin k => MMObj K a b c))
  | 0 => by
      show TensorObj.Restrict (MMObj K (0 * a) b c) TensorObj.zeroObj
      rw [show (0 : ℕ) * a = 0 from Nat.zero_mul a]
      exact MMObj_zero_restrict_zeroObj (K := K) b c
  | 1 => by
      show TensorObj.Restrict (MMObj K (1 * a) b c) (MMObj K a b c)
      exact MMObj_one_mul_restrict (K := K) a b c
  | (k + 2) => by
      show TensorObj.Restrict (MMObj K ((k + 2) * a) b c)
        (TensorObj.add (MMObj K a b c)
          (TensorObj.bigAdd (fun i : Fin (k + 1) =>
            (fun _ : Fin (k + 2) => MMObj K a b c) i.succ)))
      -- The `Fin.succ` reindexing is a constant function, so it stays MMObj K a b c.
      have heq_fun : (fun i : Fin (k + 1) =>
            (fun _ : Fin (k + 2) => MMObj K a b c) i.succ) =
          (fun _ : Fin (k + 1) => MMObj K a b c) := by funext _; rfl
      rw [heq_fun]
      have ih : TensorObj.Restrict (MMObj K ((k + 1) * a) b c)
          (TensorObj.bigAdd (fun _ : Fin (k + 1) => MMObj K a b c)) :=
        mme_bigAdd_identical_MM_to_flat_MM_aux a b c (k + 1)
      have h_add_func : TensorObj.Restrict
          (TensorObj.add (MMObj K a b c) (MMObj K ((k + 1) * a) b c))
          (TensorObj.add (MMObj K a b c)
            (TensorObj.bigAdd (fun _ : Fin (k + 1) => MMObj K a b c))) :=
        restrict_add_congr (restrict_refl _) ih
      have h_merge : TensorObj.Restrict (MMObj K (a + (k + 1) * a) b c)
          (TensorObj.add (MMObj K a b c) (MMObj K ((k + 1) * a) b c)) :=
        MMObj_add_restrict (K := K) a ((k + 1) * a) b c
      have harith : a + (k + 1) * a = (k + 2) * a := by ring
      rw [harith] at h_merge
      exact restrict_trans h_merge h_add_func

/-- **Main theorem.** `MMObj K (k * a) b c` is restricted from
`bigAdd (fun _ : Fin k => MMObj K a b c)`. -/
theorem solution {K : Type u} [Field K] (k a b c : ℕ) :
    TensorObj.Restrict
      (MMObj K (k * a) b c)
      (TensorObj.bigAdd (fun _ : Fin k => MMObj K a b c)) :=
  mme_bigAdd_identical_MM_to_flat_MM_aux a b c k
