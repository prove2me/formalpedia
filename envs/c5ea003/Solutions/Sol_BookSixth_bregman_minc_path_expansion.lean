-- Prove2me | solution 1 for BookSixth.bregman_minc_path_expansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:01:23.677568+00:00
-- url     : https://prove2.me/submissions/e1c0b63c-6604-4024-b23d-f8cb6477d36f

import Mathlib
import Definitions.Def_BregmanMincWeights

open scoped BigOperators
open BregmanMincWeights

/- Work in progress for the path-expansion child. This file proves helper
statements only; it is not a solution to the canonical target. -/
namespace BookPathExpansion

def choices {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (i : Fin n) (unused : Finset (Fin n)) : Finset (Fin n) :=
  unused.filter (fun j => A i j = 1)

def paths {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    List (Fin n) → Finset (Fin n) → Finset (List (Fin n))
  | [], _ => {[]}
  | i :: rows, unused =>
      (choices A i unused).biUnion fun j =>
        (paths A rows (unused.erase j)).image (List.cons j)

noncomputable def weight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    List (Fin n) → Finset (Fin n) → List (Fin n) → ℝ
  | [], _, [] => 1
  | i :: rows, unused, j :: cols =>
      weight A rows (unused.erase j) cols / ((choices A i unused).card : ℝ)
  | _, _, _ => 0

theorem paths_cons_disjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (rows : List (Fin n)) (unused : Finset (Fin n))
    {j k : Fin n} (hjk : j ≠ k) :
    Disjoint ((paths A rows (unused.erase j)).image (List.cons j))
      ((paths A rows (unused.erase k)).image (List.cons k)) := by
  apply Finset.disjoint_left.2
  intro cols hj hk
  rcases Finset.mem_image.1 hj with ⟨xs, _, hxs⟩
  rcases Finset.mem_image.1 hk with ⟨ys, _, hys⟩
  exact hjk (List.cons.inj (hxs.trans hys.symm)).1

theorem paths_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (rows : List (Fin n)) (unused : Finset (Fin n))
    (cols : List (Fin n)) (h : cols ∈ paths A rows unused) :
    cols.length = rows.length := by
  induction rows generalizing unused cols with
  | nil =>
      have hc : cols = [] := by simpa [paths] using h
      simp [hc]
  | cons i rows ih =>
      rcases Finset.mem_biUnion.1 h with ⟨j, _, hj⟩
      rcases Finset.mem_image.1 hj with ⟨tail, ht, rfl⟩
      simp only [List.length_cons, ih _ _ ht]

theorem sum_paths_eq_recursion {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ)
    (F : List (Fin n) → Finset (Fin n) → ℝ)
    (hnil : ∀ unused, F [] unused = 1)
    (hcons : ∀ i rows unused, F (i :: rows) unused =
      (∑ j ∈ choices A i unused, F rows (unused.erase j)) /
        ((choices A i unused).card : ℝ))
    (rows : List (Fin n)) (unused : Finset (Fin n)) :
    (∑ cols ∈ paths A rows unused, weight A rows unused cols) = F rows unused := by
  classical
  induction rows generalizing unused with
  | nil => simp [paths, weight, hnil]
  | cons i rows ih =>
      rw [paths, Finset.sum_biUnion]
      · calc
          (∑ j ∈ choices A i unused,
              ∑ cols ∈ (paths A rows (unused.erase j)).image (List.cons j),
                weight A (i :: rows) unused cols) =
              ∑ j ∈ choices A i unused,
                (∑ cols ∈ paths A rows (unused.erase j),
                  weight A rows (unused.erase j) cols) /
                    ((choices A i unused).card : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Finset.sum_image]
                  · simp only [weight, Finset.sum_div]
                  · intro xs _ ys _ heq
                    exact (List.cons.inj heq).2
          _ = (∑ j ∈ choices A i unused, F rows (unused.erase j)) /
                ((choices A i unused).card : ℝ) := by
                  simp only [ih, Finset.sum_div]
          _ = F (i :: rows) unused := (hcons i rows unused).symm
      · intro j _ k _ hjk
        exact paths_cons_disjoint A rows unused hjk

theorem choices_image_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (remaining : Finset (Fin n)) :
    choices A i (remaining.image σ) =
      (remaining.filter (fun t => A i (σ t) = 1)).image σ := by
  ext j
  simp only [choices, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hA⟩
    exact ⟨t, ⟨ht, hA⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hA⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, hA⟩

theorem choices_card_eq_avail {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ π : Equiv.Perm (Fin n)) (i : Fin n) :
    (choices A i ((Finset.univ.filter (fun t => π.symm i ≤ π.symm t)).image σ)).card =
      avail i (preS A σ i) π := by
  classical
  rw [choices_image_eq, Finset.card_image_of_injective _ σ.injective]
  unfold avail
  congr 1
  ext t
  simp [preS, and_comm]

theorem mem_paths_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (rows : List (Fin n)) (unused : Finset (Fin n)) (cols : List (Fin n)) :
    cols ∈ paths A rows unused ↔
      cols.Nodup ∧ (∀ j ∈ cols, j ∈ unused) ∧
        List.Forall₂ (fun i j => A i j = 1) rows cols := by
  induction rows generalizing unused cols with
  | nil =>
      cases cols <;> simp [paths]
  | cons i rows ih =>
      cases cols with
      | nil => simp [paths]
      | cons j cols =>
          have hstep : j :: cols ∈ paths A (i :: rows) unused ↔
              j ∈ choices A i unused ∧ cols ∈ paths A rows (unused.erase j) := by
            simp [paths, Finset.mem_biUnion, Finset.mem_image]
          rw [hstep, ih]
          simp only [choices, Finset.mem_filter, Finset.mem_erase,
            List.nodup_cons, List.forall_mem_cons, List.forall₂_cons]
          constructor
          · rintro ⟨⟨hju, hij⟩, hnd, hmem, hrel⟩
            refine ⟨⟨?_, hnd⟩, ⟨hju, ?_⟩, hij, hrel⟩
            · intro hj
              exact (hmem j hj).1 rfl
            · intro k hk
              exact (hmem k hk).2
          · rintro ⟨⟨hjnot, hnd⟩, ⟨hju, hmem⟩, hij, hrel⟩
            refine ⟨⟨hju, hij⟩, hnd, ?_, hrel⟩
            intro k hk
            refine ⟨?_, hmem k hk⟩
            intro hkj
            exact hjnot (hkj ▸ hk)

theorem recursion_unique {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (F G : List (Fin n) → Finset (Fin n) → ℝ)
    (hF0 : ∀ U, F [] U = 1) (hG0 : ∀ U, G [] U = 1)
    (hFs : ∀ i rows U, F (i :: rows) U =
      (∑ j ∈ choices A i U, F rows (U.erase j)) / ((choices A i U).card : ℝ))
    (hGs : ∀ i rows U, G (i :: rows) U =
      (∑ j ∈ choices A i U, G rows (U.erase j)) / ((choices A i U).card : ℝ)) :
    F = G := by
  funext rows U
  induction rows generalizing U with
  | nil => rw [hF0, hG0]
  | cons i rows ih => simp only [hFs, hGs, ih]

theorem exists_perm_ofFn {n : ℕ} (cols : List (Fin n))
    (hnd : cols.Nodup) (hlen : cols.length = n) :
    ∃ τ : Equiv.Perm (Fin n), List.ofFn τ = cols := by
  classical
  have hcard : cols.toFinset.card = (Finset.univ : Finset (Fin n)).card := by
    simpa [List.toFinset_card_of_nodup hnd] using hlen
  have hfull : ∀ j : Fin n, j ∈ cols := by
    have heq : cols.toFinset = Finset.univ :=
      (Finset.eq_iff_card_le_of_subset (Finset.subset_univ _)).1 hcard.ge
    intro j
    have hj : j ∈ cols.toFinset := heq.symm ▸ Finset.mem_univ j
    simpa using hj
  let e := List.Nodup.getEquivOfForallMemList cols hnd hfull
  let τ : Equiv.Perm (Fin n) :=
    { toFun := fun k => e (Fin.cast hlen.symm k)
      invFun := fun j => Fin.cast hlen (e.symm j)
      left_inv := by intro k; simp
      right_inv := by intro j; simp }
  refine ⟨τ, ?_⟩
  apply List.ext_get
  · simpa using hlen.symm
  · intro k hk₁ hk₂
    simp [List.get_ofFn, τ, e, List.Nodup.getEquivOfForallMemList] <;> rfl

theorem full_path_has_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (π : Equiv.Perm (Fin n)) (cols : List (Fin n))
    (hcols : cols ∈ paths A (List.ofFn π) Finset.univ) :
    ∃ σ ∈ aSys A, List.ofFn (fun k => σ (π k)) = cols := by
  classical
  obtain ⟨hnd, _, hrel⟩ := (mem_paths_iff A _ _ _).1 hcols
  have hlen : cols.length = n := by
    simpa using paths_length A _ _ _ hcols
  obtain ⟨τ, hτ⟩ := exists_perm_ofFn cols hnd hlen
  let σ := π.symm.trans τ
  have hσ : σ ∈ aSys A := by
    simp only [aSys, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have hk₁ : (π.symm i).val < (List.ofFn π).length := by simp
    have hrelτ : List.Forall₂ (fun i j => A i j = 1) (List.ofFn π) (List.ofFn τ) := by
      simpa only [hτ] using hrel
    have hk₂ : (π.symm i).val < (List.ofFn τ).length := by simp
    have hi := hrelτ.get hk₁ hk₂
    simpa [List.get_ofFn, σ] using hi
  refine ⟨σ, hσ, ?_⟩
  have hf : (fun k => σ (π k)) = (fun k => τ k) := by
    funext k
    simp [σ]
  simpa only [hf] using hτ

theorem path_code_injective {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      List.ofFn (fun k => σ (π k))) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hk : (π.symm i).val < n := (π.symm i).isLt
  have hi := congrArg (fun xs : List (Fin n) => xs[(π.symm i).val]?) h
  simpa [hk] using hi

theorem perm_has_full_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ π : Equiv.Perm (Fin n)) (hσ : σ ∈ aSys A) :
    List.ofFn (fun k => σ (π k)) ∈ paths A (List.ofFn π) Finset.univ := by
  apply (mem_paths_iff A _ _ _).2
  refine ⟨List.nodup_ofFn_ofInjective (σ.injective.comp π.injective), ?_, ?_⟩
  · intro j _
    exact Finset.mem_univ j
  · have ha : ∀ i, A i (σ i) = 1 := (Finset.mem_filter.1 hσ).2
    rw [List.ofFn_eq_map, List.ofFn_eq_map,
      List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro k _
    exact ha (π k)

noncomputable def suffixWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) : List (Fin n) → ℝ
  | [] => 1
  | i :: rows => suffixWeight A σ rows /
      ((choices A i ((i :: rows).toFinset.image σ)).card : ℝ)

theorem erase_image_cons {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (rows : List (Fin n)) (hi : i ∉ rows) :
    ((i :: rows).toFinset.image σ).erase (σ i) = rows.toFinset.image σ := by
  classical
  have hnot : σ i ∉ rows.toFinset.image σ := by
    simp only [Finset.mem_image, List.mem_toFinset]
    rintro ⟨j, hj, heq⟩
    exact hi (σ.injective heq ▸ hj)
  simp [hnot]

theorem weight_map_eq_suffixWeight {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (rows : List (Fin n)) (hrows : rows.Nodup) :
    weight A rows (rows.toFinset.image σ) (rows.map σ) = suffixWeight A σ rows := by
  induction rows with
  | nil => simp [weight, suffixWeight]
  | cons i rows ih =>
      obtain ⟨hi, hnd⟩ := List.nodup_cons.1 hrows
      simp only [List.map_cons, weight, suffixWeight, erase_image_cons σ i rows hi, ih hnd]

/- The only mathematical hypothesis still exposed in this assembly is the
full-order suffix-product identity. This is not the canonical solution. -/
theorem assemble_path_expansion {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ) (π : Equiv.Perm (Fin n))
    (F : List (Fin n) → Finset (Fin n) → ℝ)
    (hnil : ∀ U, F [] U = 1)
    (hcons : ∀ i rows U, F (i :: rows) U =
      (∑ j ∈ choices A i U, F rows (U.erase j)) / ((choices A i U).card : ℝ))
    (hweight : ∀ σ ∈ aSys A,
      weight A (List.ofFn π) Finset.univ (List.ofFn (fun k => σ (π k))) = qW A σ π) :
    (∑ σ ∈ aSys A, qW A σ π) = F (List.ofFn π) Finset.univ := by
  classical
  have himage : (aSys A).image (fun σ => List.ofFn (fun k => σ (π k))) =
      paths A (List.ofFn π) Finset.univ := by
    ext cols
    constructor
    · rintro h
      rcases Finset.mem_image.1 h with ⟨σ, hσ, rfl⟩
      exact perm_has_full_path A σ π hσ
    · intro h
      obtain ⟨σ, hσ, heq⟩ := full_path_has_perm A π cols h
      exact Finset.mem_image.2 ⟨σ, hσ, heq⟩
  calc
    (∑ σ ∈ aSys A, qW A σ π) =
        ∑ σ ∈ aSys A,
          weight A (List.ofFn π) Finset.univ (List.ofFn (fun k => σ (π k))) :=
      Finset.sum_congr rfl (fun σ hσ => (hweight σ hσ).symm)
    _ = ∑ cols ∈ (aSys A).image (fun σ => List.ofFn (fun k => σ (π k))),
          weight A (List.ofFn π) Finset.univ cols :=
      (Finset.sum_image (path_code_injective π).injOn).symm
    _ = F (List.ofFn π) Finset.univ := by
      rw [himage]
      exact sum_paths_eq_recursion A F hnil hcons _ _

theorem suffixWeight_eq_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ π : Equiv.Perm (Fin n)) (rows : List (Fin n))
    (hs : rows.Pairwise (fun i j => π.symm i < π.symm j)) :
    suffixWeight A σ rows =
      (rows.map (fun i => (1 : ℝ) /
        ((choices A i ((rows.toFinset.filter (fun t => π.symm i ≤ π.symm t)).image σ)).card : ℝ))).prod := by
  classical
  induction rows with
  | nil => simp [suffixWeight]
  | cons i rows ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hs
      have hfirst : (i :: rows).toFinset.filter (fun t => π.symm i ≤ π.symm t) =
          (i :: rows).toFinset := by
        apply Finset.filter_eq_self.2
        intro t ht
        simp only [List.mem_toFinset, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact le_rfl
        · exact (hhead t ht).le
      have hrest : ∀ j ∈ rows,
          (i :: rows).toFinset.filter (fun t => π.symm j ≤ π.symm t) =
            rows.toFinset.filter (fun t => π.symm j ≤ π.symm t) := by
        intro j hj
        ext t
        have hji := not_le_of_gt (hhead j hj)
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons]
        constructor
        · rintro ⟨rfl | ht, hle⟩
          · exact False.elim (hji hle)
          · exact ⟨ht, hle⟩
        · rintro ⟨ht, hle⟩
          exact ⟨Or.inr ht, hle⟩
      rw [suffixWeight, List.map_cons, List.prod_cons, hfirst, ih htail]
      have hm : (rows.map (fun j => (1 : ℝ) /
          ((choices A j (((i :: rows).toFinset.filter (fun t => π.symm j ≤ π.symm t)).image σ)).card : ℝ))) =
          rows.map (fun j => (1 : ℝ) /
            ((choices A j ((rows.toFinset.filter (fun t => π.symm j ≤ π.symm t)).image σ)).card : ℝ)) := by
        apply List.map_congr_left
        intro j hj
        rw [hrest j hj]
      rw [hm]
      ring

theorem full_weight_eq_qW {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ π : Equiv.Perm (Fin n)) :
    weight A (List.ofFn π) Finset.univ (List.ofFn (fun k => σ (π k))) = qW A σ π := by
  classical
  have hfull : (List.ofFn π).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_univ, iff_true]
    exact π.surjective i
  have himage : ((List.ofFn π).toFinset.image σ) = Finset.univ := by
    rw [hfull]
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact σ.surjective i
  have hs : (List.ofFn π).Pairwise (fun i j => π.symm i < π.symm j) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    simpa using hij
  have hw := weight_map_eq_suffixWeight A σ (List.ofFn π)
    (List.nodup_ofFn_ofInjective π.injective)
  rw [himage, List.map_ofFn] at hw
  simp only [Function.comp_def] at hw
  rw [hw, suffixWeight_eq_product A σ π _ hs, hfull]
  simp_rw [choices_card_eq_avail]
  rw [List.map_ofFn, List.prod_ofFn]
  exact Equiv.prod_comp π (fun i => (1 : ℝ) / (avail i (preS A σ i) π : ℝ))

end BookPathExpansion

open BookPathExpansion

theorem solution : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ)
    (π : Equiv.Perm (Fin n)) (F : List (Fin n) → Finset (Fin n) → ℝ),
    (∀ unused, F [] unused = 1) →
    (∀ i rows unused, F (i :: rows) unused =
      (∑ j ∈ unused.filter (fun j => A i j = 1), F rows (unused.erase j)) /
        ((unused.filter (fun j => A i j = 1)).card : ℝ)) →
    ∑ σ ∈ aSys A, qW A σ π = F ((List.finRange n).map π) Finset.univ := by
  intro n A π F hnil hcons
  rw [← List.ofFn_eq_map]
  exact assemble_path_expansion A π F hnil hcons (fun σ _ => full_weight_eq_qW A σ π)
