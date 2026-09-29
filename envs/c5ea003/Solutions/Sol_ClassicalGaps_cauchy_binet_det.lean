-- Prove2me | solution 1 for ClassicalGaps.cauchy_binet_det
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T22:07:52.87237+00:00
-- url     : https://prove2.me/submissions/9bf7b3ce-f3a3-4a43-84c7-1ddcae025577

import Mathlib
open Classical Matrix Finset

theorem solution {m n : ℕ} (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
        (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0 := by
  -- Step 1: expand det(A*B) via detRowAlternating and multilinearity over row index k
  have hstep1 : (A * B).det =
      ∑ r : Fin m → Fin n, (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det := by
    have hrow : ∀ i : Fin m, (A * B) i = ∑ k : Fin n, A i k • (B k) := by
      intro i
      funext j
      simp [Matrix.mul_apply, Finset.sum_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    calc (A * B).det = Matrix.detRowAlternating (fun i => (A * B) i) := rfl
      _ = Matrix.detRowAlternating (fun i => ∑ k : Fin n, A i k • (B k)) := by
          congr 1; funext i; exact hrow i
      _ = ∑ r : Fin m → Fin n, Matrix.detRowAlternating (fun i => A i (r i) • B (r i)) :=
          MultilinearMap.map_sum _ _
      _ = ∑ r : Fin m → Fin n, (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det := by
          apply Finset.sum_congr rfl
          intro r _
          have := Matrix.detRowAlternating.map_smul_univ (fun i : Fin m => A i (r i)) (fun i : Fin m => B (r i))
          rw [smul_eq_mul] at this
          rw [this]
          rfl
  set F : (Fin m → Fin n) → ℝ := fun r => (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det with hF
  -- Step 2: non-injective r contribute 0 to the sum
  have hstep2 : ∀ r : Fin m → Fin n, ¬ Function.Injective r → F r = 0 := by
    intro r hr
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hr
    simp only [hF]
    have heqrow : (Matrix.of (fun k : Fin m => B (r k))) p = (Matrix.of (fun k : Fin m => B (r k))) q := by
      show B (r p) = B (r q)
      rw [hpq]
    rw [Matrix.det_zero_of_row_eq hne heqrow]
    ring
  -- Step 3: filtering to injective r
  have hstep3 : (∑ r : Fin m → Fin n, F r) = ∑ r ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective, F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : Function.Injective r
    · simp [hr]
    · simp [hr, hstep2 r hr]
  -- Step 4: regroup the injective sum by image S, then by permutation τ
  have hmaps : ∀ r ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective,
      Finset.image r Finset.univ ∈ (Finset.univ : Finset (Fin n)).powersetCard m := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hr.2, Finset.card_univ, Fintype.card_fin]
  have hstep4 : (∑ r ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective, F r)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ∑ r ∈ ((Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
              (fun r => Finset.image r Finset.univ = S), F r := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps F]
  -- Step 5: for fixed S, bijection between the fiber and permutations of Fin m
  have hstep5 : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (∑ r ∈ ((Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
              (fun r => Finset.image r Finset.univ = S), F r)
      = (if hS : S.card = m then
          (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
          (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
        else 0) := by
    intro S hS_mem
    have hS : S.card = m := (Finset.mem_powersetCard.mp hS_mem).2
    rw [dif_pos hS]
    set coeσ : Fin m → Fin n := fun i => (S.orderIsoOfFin hS i : Fin n) with hcoeσ
    have hcoeσ_inj : Function.Injective coeσ := by
      intro i j hij
      exact (S.orderIsoOfFin hS).injective (Subtype.ext hij)
    have hcoeσ_mem : ∀ i, coeσ i ∈ S := fun i => (S.orderIsoOfFin hS i).2
    have hcoeσ_image : Finset.image coeσ Finset.univ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
        rw [← hi]; exact hcoeσ_mem i
      · rw [Finset.card_image_of_injective _ hcoeσ_inj, Finset.card_univ, Fintype.card_fin, hS]
    set As : Matrix (Fin m) (Fin m) ℝ := A.submatrix id coeσ with hAs
    set Bs : Matrix (Fin m) (Fin m) ℝ := B.submatrix coeσ id with hBs
    set fiber : Finset (Fin m → Fin n) :=
      ((Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
        (fun r => Finset.image r Finset.univ = S) with hfiber
    have hmemT : ∀ τ : Equiv.Perm (Fin m), coeσ ∘ τ ∈ fiber := by
      intro τ
      rw [hfiber, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, hcoeσ_inj.comp τ.injective⟩, ?_⟩
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hx
        rw [← hk]; exact hcoeσ_mem (τ k)
      · rw [Finset.card_image_of_injective _ (hcoeσ_inj.comp τ.injective), Finset.card_univ,
          Fintype.card_fin, hS]
    -- for each r in the fiber, build the unique permutation τ with coeσ ∘ τ = r
    have hbuild : ∀ r ∈ fiber, ∃ τ : Equiv.Perm (Fin m), coeσ ∘ τ = r := by
      intro r hr
      rw [hfiber, Finset.mem_filter, Finset.mem_filter] at hr
      obtain ⟨⟨-, hrinj⟩, himg⟩ := hr
      have hforward : ∀ k : Fin m, ∃ l : Fin m, coeσ l = r k := by
        intro k
        have hmem : r k ∈ S := by
          rw [← himg]; exact Finset.mem_image_of_mem r (Finset.mem_univ k)
        rw [← hcoeσ_image] at hmem
        obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hmem
        exact ⟨l, hl⟩
      choose g hg using hforward
      have hg_inj : Function.Injective g := by
        intro a b hab
        apply hrinj
        rw [← hg a, ← hg b, hab]
      have hg_bij : Function.Bijective g := (Finite.injective_iff_bijective).mp hg_inj
      exact ⟨Equiv.ofBijective g hg_bij, funext hg⟩
    choose τ_of hτ_of using hbuild
    have huniq : ∀ (r : Fin m → Fin n) (hr : r ∈ fiber) (τ : Equiv.Perm (Fin m)),
        coeσ ∘ τ = r → τ = τ_of r hr := by
      intro r hr τ hτ
      apply Equiv.ext
      intro k
      apply hcoeσ_inj
      have h1 : coeσ (τ k) = r k := congrFun hτ k
      have h2 : coeσ (τ_of r hr k) = r k := congrFun (hτ_of r hr) k
      rw [h1, h2]
    have hbij : (∑ r ∈ fiber, F r) = ∑ τ : Equiv.Perm (Fin m), F (coeσ ∘ τ) := by
      apply Finset.sum_bij' (fun r hr => τ_of r hr) (fun τ _ => coeσ ∘ τ)
      case hi => intro r _; exact Finset.mem_univ _
      case hj => intro τ _; exact hmemT τ
      case left_neg => intro r hr; exact hτ_of r hr
      case right_neg => intro τ _; exact (huniq (coeσ ∘ τ) (hmemT τ) τ rfl).symm
      case h => intro r hr; rw [hτ_of r hr]
    rw [hbij]
    -- now compute the sum over τ directly
    have hBdet : ∀ τ : Equiv.Perm (Fin m), (Matrix.of (fun i : Fin m => B ((coeσ ∘ τ) i))).det
        = Equiv.Perm.sign τ * Bs.det := by
      intro τ
      have heq : (Matrix.of (fun i : Fin m => B ((coeσ ∘ τ) i))) = Bs.submatrix τ id := by
        ext i j
        simp [Bs, Matrix.submatrix_apply, Function.comp_apply]
      rw [heq, Matrix.det_permute]
    have hAsum : As.det = ∑ τ : Equiv.Perm (Fin m), Equiv.Perm.sign τ * ∏ i : Fin m, A i ((coeσ ∘ τ) i) := by
      rw [← Matrix.det_transpose As, Matrix.det_apply']
      apply Finset.sum_congr rfl
      intro τ _
      simp [As, Matrix.transpose_apply, Matrix.submatrix_apply, Function.comp_apply]
    calc (∑ τ : Equiv.Perm (Fin m), F (coeσ ∘ τ))
        = ∑ τ : Equiv.Perm (Fin m), (∏ i : Fin m, A i ((coeσ ∘ τ) i)) *
            (Equiv.Perm.sign τ * Bs.det) := by
          apply Finset.sum_congr rfl
          intro τ _
          simp only [hF]
          rw [hBdet τ]
      _ = Bs.det * ∑ τ : Equiv.Perm (Fin m), Equiv.Perm.sign τ * ∏ i : Fin m, A i ((coeσ ∘ τ) i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          ring
      _ = Bs.det * As.det := by rw [← hAsum]
      _ = As.det * Bs.det := by ring
  rw [hstep1, hstep3, hstep4]
  apply Finset.sum_congr rfl
  intro S hS_mem
  exact hstep5 S hS_mem
