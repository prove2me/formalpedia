-- Prove2me | solution 1 for mme_released_global_yz_expression_data_1_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:39:47.136764+00:00
-- url     : https://prove2.me/submissions/45435429-0ce7-47d3-ac47-8e441c2720fc

import Definitions.Def_mme_released_global_yz_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option profiler true
attribute [local irreducible] alpha cachedCounts shapeVector jointRows entries wordQ gradeQ interiorQ

private def gradeFast (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) : ℚ :=
  ((∑ s : Fin 45, if shapeVector s (RecursiveYZ.yzMode i) = j then alpha o s * cachedCounts o i s t else 0 : ℕ) : ℚ) / (denominator : ℚ)^5
private def interiorFast (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) : ℚ :=
  ((∑ s : Fin 45, if ¬ boundary i s ∧ shapeVector s (RecursiveYZ.yzMode i) = j then alpha o s * cachedCounts o i s t else 0 : ℕ) : ℚ) / (denominator : ℚ)^5
private theorem sum_ratio {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℕ) (d : ℚ) :
    (∑ s, if p s then (f s : ℚ)/d else 0) = ((∑ s, if p s then f s else 0 : ℕ) : ℚ)/d := by
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp
private theorem grade_fast : gradeQ = gradeFast := by
  funext o i j t
  unfold gradeQ wordQ gradeFast
  exact sum_ratio (fun s ↦ shapeVector s (RecursiveYZ.yzMode i) = j)
    (fun s ↦ alpha o s * cachedCounts o i s t) ((denominator : ℚ)^5)
private theorem interior_fast : interiorQ = interiorFast := by
  funext o i j t
  unfold interiorQ wordQ interiorFast
  exact sum_ratio (fun s ↦ ¬ boundary i s ∧ shapeVector s (RecursiveYZ.yzMode i) = j)
    (fun s ↦ alpha o s * cachedCounts o i s t) ((denominator : ℚ)^5)
private def rawFast (o : Fin 6) (i : Fin 2) : Terms :=
  massTerms (List.ofFn (marginalQ o (RecursiveYZ.yzMode i))) ++
  (List.ofFn (fun j : Fin 9 ↦ massTerms (List.ofFn (gradeFast o i j)))).flatten ++
  negative ((List.ofFn (fun s : Fin 45 ↦ if boundary i s then massTerms (List.ofFn (wordQ o i s)) else [])).flatten) ++
  negative ((List.ofFn (fun j : Fin 9 ↦ massTerms (List.ofFn (interiorFast o i j)))).flatten)
private theorem raw_fast (o : Fin 6) (i : Fin 2) : rawTerms o i = rawFast o i := by
  simp only [rawTerms,rawFast,grade_fast,interior_fast]
private theorem certified : (entries (1 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawFast (1 : Fin 6) (0 : Fin 2)) := by
  decide +kernel

theorem solution :
    ((entries (1 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (1 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (1 : Fin 6) ≤ totalBound (1 : Fin 6) (0 : Fin 2)) := by
  constructor
  · exact certified.trans (congrArg prune (raw_fast (1 : Fin 6) (0 : Fin 2)).symm)
  · decide +kernel
