-- Prove2me | solution 1 for mme_released_global_yz_cached_counts_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:23:13.414984+00:00
-- url     : https://prove2.me/submissions/2408e2e6-b885-47cc-94bc-7590b1af7a29

import Definitions.Def_mme_released_global_yz_word_data
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option profiler true

private def hist {W : Type*} [DecidableEq W] (t : W) (l : List (W × ℕ)) : ℕ :=
  (l.map (fun p ↦ if p.1 = t then p.2 else 0)).sum
private def insertWeight {W : Type*} [LinearOrder W] (a : W × ℕ) : List (W × ℕ) → List (W × ℕ)
  | [] => [a]
  | b :: l => if a.1 = b.1 then (b.1,a.2+b.2) :: l
    else if a.1 < b.1 then a :: b :: l else b :: insertWeight a l
private def compress {W : Type*} [LinearOrder W] (l : List (W × ℕ)) : List (W × ℕ) :=
  l.foldr insertWeight []
private theorem hist_insert {W : Type*} [LinearOrder W] (a : W × ℕ) (l : List (W × ℕ)) (t : W) :
    hist t (insertWeight a l) = (if a.1 = t then a.2 else 0) + hist t l := by
  induction l with
  | nil => simp [hist,insertWeight]
  | cons b l ih =>
    by_cases hab : a.1 = b.1
    · simp only [insertWeight,if_pos hab,hist,List.map_cons,List.sum_cons]
      by_cases hbt : b.1 = t <;> simp [hab,hbt] <;> omega
    · by_cases hlt : a.1 < b.1
      · simp [insertWeight,hab,hlt,hist]
      · simp only [insertWeight,if_neg hab,if_neg hlt,hist,List.map_cons,List.sum_cons] at *
        rw [ih]
        omega
private theorem hist_compress {W : Type*} [LinearOrder W] (l : List (W × ℕ)) (t : W) :
    hist t (compress l) = hist t l := by
  induction l with
  | nil => simp [compress,hist]
  | cons a l ih =>
    change hist t (insertWeight a (compress l)) = _
    rw [hist_insert,ih]
    rfl
private theorem hist_filter {W : Type*} [DecidableEq W] (l : List (W × ℕ)) (t : W) :
    hist t (l.filter (fun p ↦ p.2 != 0)) = hist t l := by
  induction l with
  | nil => simp [hist]
  | cons a l ih =>
    by_cases ha : a.2 = 0
    · simpa [hist,ha] using ih
    · simpa [hist,ha] using congrArg (fun n ↦ (if a.1 = t then a.2 else 0)+n) ih

attribute [local irreducible] wordEquiv atom cachedCounts

private def atomCode (a : Fin 1296) (i : Fin 3) : Fin 81 :=
  ⟨wordIndex (atom a i) % 81, Nat.mod_lt _ (by decide)⟩
private theorem atom_code (a : Fin 1296) (i : Fin 3) : codeWord (atomCode a i) = atom a i := by
  have hl : ∀ t : Fin 81, wordIndex (codeWord t) = t.val := by decide +kernel
  obtain ⟨t,ht⟩ := wordEquiv.surjective (atom a i)
  have he (t : Fin 81) : wordEquiv t = codeWord t := by simp only [wordEquiv,Equiv.ofBijective_apply]
  rw [he] at ht
  have hc : atomCode a i = t := by
    apply Fin.ext
    change wordIndex (atom a i) % 81 = t.val
    rw [← ht,hl,Nat.mod_eq_of_lt t.isLt]
  rw [hc]
  exact ht

private def cachedRows (o : Fin 6) (i : Fin 2) (s : Fin 45) : List (Fin 81 × ℕ) :=
  (List.ofFn (fun t : Fin 81 ↦ (t,cachedCounts o i s t))).filter (fun p ↦ p.2 != 0)
private theorem hist_ofFn {n : ℕ} (f : Fin n → ℕ) (t : Fin n) :
    hist t (List.ofFn (fun j ↦ (j,f j))) = f t := by
  unfold hist
  rw [List.map_ofFn,List.sum_ofFn]
  change (∑ j : Fin n, if j = t then f j else 0) = f t
  rw [Finset.sum_eq_single t]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem dense_valid (o : Fin 6) (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts o i s t = hist t (cachedRows o i s) := by
  unfold cachedRows
  rw [hist_filter]
  exact (hist_ofFn (cachedCounts o i s) t).symm
private theorem compressed_valid : ∀ i s, cachedRows (0 : Fin 6) i s =
    compress ((jointRows (0 : Fin 6) s).map (fun a ↦ (atomCode a.1 (RecursiveYZ.yzMode i),a.2))) := by
  intro i
  fin_cases i <;> decide +kernel

attribute [local irreducible] cachedRows jointRows

theorem solution (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts (0 : Fin 6) i s t =
      ((jointRows (0 : Fin 6) s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum := by
  rw [dense_valid,compressed_valid,hist_compress]
  unfold hist
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a _
  have hc : atomCode a.1 (RecursiveYZ.yzMode i) = t ↔ atom a.1 (RecursiveYZ.yzMode i) = codeWord t := by
    rw [← atom_code]
    constructor
    · intro h
      exact congrArg codeWord h
    · intro h
      apply wordEquiv.injective
      simpa only [wordEquiv,Equiv.ofBijective_apply] using h
  simp only [hc]
