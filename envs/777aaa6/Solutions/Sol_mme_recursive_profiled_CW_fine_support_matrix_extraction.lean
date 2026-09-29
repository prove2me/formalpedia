-- Prove2me | solution 1 for mme_recursive_profiled_CW_fine_support_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:08:47.582549+00:00
-- url     : https://prove2.me/submissions/e5a71449-3703-4ee2-9cdc-f1e57ca43a7c

import Theorems.Thm_mme_recursive_profiled_CW_boundary_end

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary MME.ProfiledCW

private def singletonProfile (g : Fin 3) : Boundary.Profile 1 1 where
  index := g.val
  index_le := by simpa using Nat.le_of_lt_succ g.isLt
  count := fun s ↦ if s = (fun _ ↦ g) then 1 else 0
  total := by
    classical
    simp
  supported := by
    classical
    intro s hs
    have h : s = fun _ ↦ g := by simpa using hs
    subst s
    simp [CWCells.grade]

private theorem singletonProfile_dim (g : Fin 3) :
    (singletonProfile g).dim = if g = 1 then 5 else 1 := by
  classical
  have hf (s : CompleteWord 1) : (if s = (fun _ ↦ g) then 1 else 0).factorial = 1 := by
    split_ifs <;> decide
  simp only [Profile.dim, singletonProfile, hf, Finset.prod_const_one]
  fin_cases g <;> norm_num [Boundary.ones]

private theorem singleton_dimensions (z t : Fin 3) :
    (singletonProfile t).a z =
      (if (singletonProfile t).shape z 0 = 1 ∧ (singletonProfile t).shape z 2 = 1 then 5 else 1) ∧
    (singletonProfile t).b z =
      (if (singletonProfile t).shape z 0 = 1 ∧ (singletonProfile t).shape z 1 = 1 then 5 else 1) ∧
    (singletonProfile t).c z =
      (if (singletonProfile t).shape z 1 = 1 ∧ (singletonProfile t).shape z 2 = 1 then 5 else 1) := by
  simp only [Profile.a, Profile.b, Profile.c, singletonProfile_dim, Profile.shape]
  fin_cases z <;> fin_cases t <;> decide

private theorem zero_mode_profile (g : Fin 3 → Fin 3)
    (hs : (g 0).val + (g 1).val + (g 2).val = 2) :
    ∃ z t : Fin 3, (singletonProfile t).shape z = fun i ↦ (g i).val := by
  by_cases h0 : g 0 = 0
  · refine ⟨0, g 1, ?_⟩
    funext i
    fin_cases i
    · simpa [Profile.shape] using congrArg Fin.val h0.symm
    · rfl
    · change 2 * 2 ^ (1 - 1) - (g 1).val = (g 2).val
      have h := congrArg Fin.val h0
      simp only [Nat.sub_self, pow_zero, mul_one]
      omega
  · by_cases h1 : g 1 = 0
    · refine ⟨1, g 2, ?_⟩
      funext i
      fin_cases i
      · change 2 * 2 ^ (1 - 1) - (g 2).val = (g 0).val
        have h := congrArg Fin.val h1
        simp only [Nat.sub_self, pow_zero, mul_one]
        omega
      · simpa [Profile.shape] using congrArg Fin.val h1.symm
      · rfl
    · have h2 : (g 2).val = 0 := by
        have h0' : (g 0).val ≠ 0 := by simpa using h0
        have h1' : (g 1).val ≠ 0 := by simpa using h1
        omega
      refine ⟨2, g 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · change 2 * 2 ^ (1 - 1) - (g 0).val = (g 1).val
        simp only [Nat.sub_self, pow_zero, mul_one]
        omega
      · simpa [Profile.shape] using h2.symm

private def singletonPartition (N : ℕ) : CWCells.Partition (id : Fin N → Fin N) where
  parts := N
  cells := Equiv.refl _
  size := fun _ ↦ 1
  fiber := fun j ↦ {
    toFun := fun _ ↦ ⟨j, rfl⟩
    invFun := fun _ ↦ 0
    left_inv := fun x ↦ Subsingleton.elim _ _
    right_inv := by intro x; apply Subtype.ext; exact x.property.symm }

/-- A jointly supported fine-grade assignment gives an exact elementary boundary termination. -/
theorem fine_support_boundary_end {N : ℕ} (P : Predicate N)
    (x : Fin 3 → FineWord N) (hs : supported x) (hx : ∀ i, P i (x i)) :
    ∃ B : BoundaryEnd 1 N P,
      B.a = ∏ r, (if (x 0 r).val = 1 ∧ (x 2 r).val = 1 then 5 else 1) ∧
      B.b = ∏ r, (if (x 0 r).val = 1 ∧ (x 1 r).val = 1 then 5 else 1) ∧
      B.c = ∏ r, (if (x 1 r).val = 1 ∧ (x 2 r).val = 1 then 5 else 1) := by
  classical
  have h (r : Fin N) := zero_mode_profile (fun i ↦ x i r) (hs r)
  choose z t ht using h
  let B : BoundaryEnd 1 N P := {
    L := N
    cells := N
    length := by simp
    cell := id
    shape := fun r ↦ (singletonProfile (t r)).shape (z r)
    mu := fun i r ↦ (singletonProfile (t r)).mu (z r) i
    partition := singletonPartition N
    profile := fun r ↦ singletonProfile (t r)
    zeroMode := z
    shapes := fun _ ↦ rfl
    profiles := fun _ _ ↦ rfl
    inside := by
      intro i y hy
      have heq : y = x i := by
        funext r
        apply Fin.ext
        have hr := hy.1 r
        simp only [id_eq, ht r] at hr
        simpa [CWCells.grade, split, finProdFinEquiv] using hr
      rw [heq]
      exact hx i

    }
  refine ⟨B, ?_, ?_, ?_⟩
  · change (∏ r, (singletonProfile (t r)).a (z r)) = _
    apply Finset.prod_congr rfl
    intro r hr
    rw [(singleton_dimensions (z r) (t r)).1, ht r]
  · change (∏ r, (singletonProfile (t r)).b (z r)) = _
    apply Finset.prod_congr rfl
    intro r hr
    rw [(singleton_dimensions (z r) (t r)).2.1, ht r]
  · change (∏ r, (singletonProfile (t r)).c (z r)) = _
    apply Finset.prod_congr rfl
    intro r hr
    rw [(singleton_dimensions (z r) (t r)).2.2, ht r]

/-- A supported fine-grade assignment yields a matrix tensor with explicit powers of five. -/
theorem fine_support_matrix_extraction {K : Type*} [Field K] {N : ℕ}
    (P : Predicate N) (x : Fin 3 → FineWord N)
    (hs : supported x) (hx : ∀ i, P i (x i)) :
    Restrict (MMObj K
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 2 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 1 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 1 r).val = 1 ∧ (x 2 r).val = 1)).card))
      (tensor K P) := by
  classical
  obtain ⟨B, ha, hb, hc⟩ := fine_support_boundary_end P x hs hx
  have h := mme_recursive_profiled_CW_boundary_end (K := K) B
  rw [ha, hb, hc] at h
  simpa [Finset.prod_ite] using h

/-- Simultaneously supported word assignments produce a matrix inside the intact profile block. -/
theorem unbroken_matrix_extraction_of_supported_words
    {K : Type*} [Field K] {P C : Type} [Fintype P] {ell L : ℕ}
    (positions : Fin L ≃ P) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (w : Fin 3 → P → CompleteWord ell)
    (hgrade : ∀ i p, CWCells.grade (w i p) = shape (cell p) i)
    (hmu : ∀ i, Useful cell (mu i) (w i))
    (hs : ∀ p r, (w 0 p r).val + (w 1 p r).val + (w 2 p r).val = 2) :
    let x := fun i ↦ flatten positions rfl (w i)
    Restrict (MMObj K
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 2 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 1 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 1 r).val = 1 ∧ (x 2 r).val = 1)).card))
      (CWCells.unbroken K 5 ell L positions cell shape mu) := by
  classical
  let x := fun i ↦ flatten positions rfl (w i)
  let Q : Predicate (L * 2 ^ (ell - 1)) := fun i y ↦
    (∀ p, CWCells.grade (split positions rfl y p) = shape (cell p) i) ∧
      Useful cell (mu i) (split positions rfl y)
  have hsplit (i : Fin 3) : split positions rfl (x i) = w i := by
    funext p r
    simp [split, x, flatten]
  have hx : ∀ i, Q i (x i) := by
    intro i
    change (∀ p, CWCells.grade (split positions rfl (x i) p) = shape (cell p) i) ∧ _
    rw [hsplit]
    exact ⟨hgrade i, hmu i⟩
  have hsup : supported x := by
    intro r
    exact hs _ _
  have heq : tensor K Q = CWCells.unbroken K 5 ell L positions cell shape mu := by
    rfl
  rw [← heq]
  exact fine_support_matrix_extraction Q x hsup hx


theorem solution {K : Type*} [Field K] {N : ℕ}
    (P : Predicate N) (x : Fin 3 → FineWord N)
    (hs : supported x) (hx : ∀ i, P i (x i)) :
    Restrict (MMObj K
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 2 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 1 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 1 r).val = 1 ∧ (x 2 r).val = 1)).card))
      (tensor K P) := by
  exact fine_support_matrix_extraction P x hs hx
#print axioms solution
