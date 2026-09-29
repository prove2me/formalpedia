-- Prove2me | solution 1 for mme_released_global_yz_entropy_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:17:18.201287+00:00
-- url     : https://prove2.me/submissions/80aab6cf-74b6-4b37-a094-0c9636df6bda

import Definitions.Def_mme_released_global_yz_certificate
import Theorems.Thm_mme_released_global_yz_data_valid
import Theorems.Thm_mme_released_global_sparse_marginals
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.ReleasedGlobalYZ MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointRows alpha atom coarseCounts wordCounts shapeEquiv cachedCounts entries

private theorem eval_append (a b : Terms) : evaluate (a++b) = evaluate a + evaluate b := by
  simp [evaluate]
private theorem eval_flatten (l : List Terms) : evaluate l.flatten = (l.map evaluate).sum := by
  induction l with
  | nil => simp [evaluate]
  | cons a l ih => simp [eval_append,ih]
private theorem eval_negative (l : Terms) : evaluate (negative l) = -evaluate l := by
  induction l with
  | nil => simp [evaluate,negative]
  | cons p l ih =>
    simp only [negative,List.map_cons,evaluate,List.sum_cons,Rat.cast_neg,neg_mul] at *
    rw [ih]
    ring
private theorem eval_prune (l : Terms) : evaluate (prune l) = evaluate l := by
  induction l with
  | nil => simp [evaluate,prune]
  | cons p l ih =>
    by_cases hc : p.1 = 0
    · simpa [evaluate,prune,hc] using ih
    by_cases hq : p.2 = 0
    · simpa [evaluate,prune,hq] using ih
    by_cases h1 : p.2 = 1
    · simpa [evaluate,prune,h1] using ih
    simpa [evaluate,prune,hc,hq,h1] using congrArg (fun x ↦ (p.1 : ℝ)*Real.log (p.2 : ℝ)+x) ih
private theorem eval_mass {n : ℕ} (v : Fin n → ℚ) :
    evaluate (massTerms (List.ofFn v)) = massEntropy (fun t ↦ (v t : ℝ)) := by
  simp [evaluate,massTerms,massEntropy,entropy,Real.negMulLog,List.sum_ofFn,Function.comp_def]

private theorem shape_eq (s : Fin 45) : (shapeEquiv s).val = shapeVector s := by
  simp only [shapeEquiv,Equiv.ofBijective_apply,shape]
private theorem alpha_eq (o : Fin 6) (s : Fin 45) :
    (profile o).1 0 (shapeEquiv s) = (alphaQ o s : ℝ) := by
  unfold profile coarseCounts alphaQ
  simp only [Equiv.symm_apply_apply,Rat.cast_div,Rat.cast_natCast,Nat.cast_mul,Nat.cast_pow]
  norm_num [denominator]
  ring
private theorem marginal_eq (o : Fin 6) (i : Fin 3) (j : Fin 9) :
    mme_modern_marginal (fun c : Shape ↦ c.val i) ((profile o).1 0) j =
      (marginalQ o i j : ℝ) := by
  have hm (f : Shape → ℝ) : mme_modern_marginal (fun c ↦ c.val i) f j =
      ∑ c : Shape, if c.val i = j then f c else 0 := by
    unfold mme_modern_marginal
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hm,← Equiv.sum_comp shapeEquiv]
  simp only [marginalQ,Rat.cast_sum,apply_ite,Rat.cast_zero]
  apply Finset.sum_congr rfl
  intro s _
  rw [shape_eq,alpha_eq]
private theorem word_eq (o : Fin 6) (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    (profile o).2 (yzMode i) ⟨0,shapeEquiv s⟩ (wordEquiv t) = (wordQ o i s t : ℝ) := by
  change (wordCounts o (yzMode i) (shapeEquiv s) (wordEquiv t) : ℝ) / (denominator : ℝ)^5 = _
  rw [mme_released_global_sparse_marginals]
  simp only [Equiv.symm_apply_apply,wordEquiv,Equiv.ofBijective_apply]
  rw [← mme_released_global_yz_data_valid.1 o i s t]
  simp [wordQ]
private theorem boundary_eq (i : Fin 2) (s : Fin 45) :
    yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),shapeEquiv s⟩ ↔ boundary i s := by
  unfold yzBoundary yBoundary zBoundary boundary
  fin_cases i <;> simp [shape_eq]
private theorem mass_equiv (f : Word → ℝ) :
    massEntropy f = massEntropy (fun t : Fin 81 ↦ f (wordEquiv t)) := by
  unfold massEntropy entropy
  rw [← Equiv.sum_comp wordEquiv (fun w ↦ Real.negMulLog (f w)),← Equiv.sum_comp wordEquiv f]
private theorem grade_eq (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) :
    (∑ c : Shape, if c.val (yzMode i) = j then (profile o).2 (yzMode i) ⟨0,c⟩ (wordEquiv t) else 0) =
      (gradeQ o i j t : ℝ) := by
  rw [← Equiv.sum_comp shapeEquiv]
  simp only [gradeQ,Rat.cast_sum,apply_ite,Rat.cast_zero,shape_eq,word_eq]
private theorem interior_eq (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) :
    (∑ c : Shape, if ¬ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),c⟩ ∧ c.val (yzMode i) = j
      then (profile o).2 (yzMode i) ⟨0,c⟩ (wordEquiv t) else 0) = (interiorQ o i j t : ℝ) := by
  rw [← Equiv.sum_comp shapeEquiv]
  simp only [interiorQ,Rat.cast_sum,apply_ite,Rat.cast_zero,shape_eq,word_eq,boundary_eq]

private theorem raw_eq (o : Fin 6) (i : Fin 2) :
    evaluate (rawTerms o i) = (profile o).coarse (yzMode i) 0 +
      (profile o).words (yzMode i) 0 - (profile o).compat i 0 := by
  have hc : (profile o).coarse (yzMode i) 0 = evaluate (massTerms (List.ofFn (marginalQ o (yzMode i)))) := by
    rw [eval_mass]
    unfold EntropyProfile.coarse
    simp_rw [marginal_eq]
  have hw : (profile o).words (yzMode i) 0 =
      ∑ j : Fin 9, evaluate (massTerms (List.ofFn (gradeQ o i j))) := by
    unfold EntropyProfile.words
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_mass,mass_equiv]
    simp_rw [grade_eq]
  have hb : (∑ c : {c : Shape // yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),c⟩},
      massEntropy (fun w ↦ (profile o).2 (yzMode i) ⟨0,c.val⟩ w)) =
      ∑ s : Fin 45, if boundary i s then evaluate (massTerms (List.ofFn (wordQ o i s))) else 0 := by
    have hh : (∑ c : {c : Shape // yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),c⟩},
        massEntropy (fun w ↦ (profile o).2 (yzMode i) ⟨0,c.val⟩ w)) =
        ∑ c : Shape, if yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),c⟩ then massEntropy (fun w ↦ (profile o).2 (yzMode i) ⟨0,c⟩ w) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun c : Shape ↦ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0,c⟩) (Finset.univ.filter (fun c : Shape ↦ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0,c⟩)) (by intro c; simp) (fun c : Shape ↦ massEntropy (fun w : Word ↦ (profile o).2 (yzMode i) ⟨0,c⟩ w))).symm
    rw [hh,← Equiv.sum_comp shapeEquiv]
    apply Finset.sum_congr rfl
    intro s _
    simp only [boundary_eq]
    split_ifs
    · rw [eval_mass,mass_equiv]
      simp_rw [word_eq]
    · rfl
  have hi : (∑ j : Fin 9, massEntropy (fun w ↦ ∑ c : Shape,
      if ¬ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨(0 : Fin 1),c⟩ ∧ c.val (yzMode i) = j then (profile o).2 (yzMode i) ⟨0,c⟩ w else 0)) =
      ∑ j : Fin 9, evaluate (massTerms (List.ofFn (interiorQ o i j))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_mass,mass_equiv]
    simp_rw [interior_eq]
  rw [hc,hw]
  unfold EntropyProfile.compat
  rw [hb,hi]
  unfold rawTerms
  simp only [eval_append,eval_negative,eval_flatten,List.map_ofFn,List.sum_ofFn]
  have hz : evaluate ([] : Terms) = 0 := rfl
  simp only [Function.comp_apply,apply_ite,hz]
  ring

theorem solution (o : Fin 6) (i : Fin 2) :
    evaluate ((entries o i).map Prod.fst) =
      (profile o).coarse (yzMode i) 0 + (profile o).words (yzMode i) 0 - (profile o).compat i 0 := by
  rw [mme_released_global_yz_data_valid.2.1,eval_prune,raw_eq]
