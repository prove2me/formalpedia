-- Prove2me | solution 2 for EmergentGeometry.entropy_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:41:59.812561+00:00
-- url     : https://prove2.me/submissions/7083a643-9eed-431c-8b58-b461842ed64a

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicContractionCalculus
import Definitions.Def_Novelty_HolographicCyclicInequality
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {k m : ℕ} (M : HoloModel V)
    (A : Fin k → Region V) (B : Fin m → Region V) (χ : ContractionMap k m)
    (hcompat : ∀ v, M.bdry v = true → ∀ j, χ.toFun (fun i => A i v) j = B j v) :
    ∑ j, entropy M (B j) ≤ ∑ i, entropy M (A i) := by
  have hcomb : ∀ {m' n' : ℕ} (F : Fin m' → Region V) (H : Fin n' → Region V),
      (∀ u v : V, M.toBulkGraph.weight u v ≠ 0 →
        ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) →
      ∑ i, cutWeight M.toBulkGraph (H i) ≤ ∑ j, cutWeight M.toBulkGraph (F j) := by
    intro m' n' F H h
    -- pointwise comparison of the weighted separation counts
    have hpt : ∀ u v : V,
        ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v
          ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
      intro u v
      by_cases hw : M.toBulkGraph.weight u v = 0
      · simp [hw]
      · have hle : ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ)
            ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) := by
          exact_mod_cast h u v hw
        exact mul_le_mul_of_nonneg_right hle (M.toBulkGraph.weight_nonneg u v)
    -- collect each family into a single double sum
    have hcollect : ∀ {k : ℕ} (K : Fin k → Region V),
        (∑ i, cutWeight M.toBulkGraph (K i))
          = (∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v) / 2 := by
      intro k K
      simp only [cutWeight]
      rw [← Finset.sum_div]
      congr 1
      calc (∑ i, ∑ u : V, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v)
          = ∑ u : V, ∑ i, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
            Finset.sum_comm
        _ = ∑ u : V, ∑ v : V, ∑ i, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
        _ = ∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
            refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
            push_cast
            rw [Finset.sum_mul]
    rw [hcollect H, hcollect F]
    have hsum : (∑ u : V, ∑ v : V, ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v)
        ≤ ∑ u : V, ∑ v : V, ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
    linarith
  have hmin : ∀ i : Fin k, ∃ g : Region V,
      g ∈ admSet M (A i) ∧ entropy M (A i) = cutWeight M.toBulkGraph g := by
    intro i
    obtain ⟨g, hg, hge⟩ :=
      Finset.exists_mem_eq_inf' (admSet_nonempty M (A i)) (cutWeight M.toBulkGraph)
    exact ⟨g, hg, hge⟩
  choose f hf hfe using hmin
  have hadm : ∀ j : Fin m, (fun v => χ.toFun (fun i => f i v) j) ∈ admSet M (B j) := by
    intro j
    rw [mem_admSet]
    intro v hv
    show χ.toFun (fun i => f i v) j = B j v
    have hpt : (fun i => f i v) = (fun i => A i v) := by
      funext i
      exact (mem_admSet.mp (hf i)) v hv
    rw [hpt]
    exact hcompat v hv j
  have hle : ∀ j : Fin m,
      entropy M (B j) ≤ cutWeight M.toBulkGraph (fun v => χ.toFun (fun i => f i v) j) :=
    fun j => Finset.inf'_le _ (hadm j)
  have hcontract : ∀ u v : V, M.toBulkGraph.weight u v ≠ 0 →
      ∑ j, sepBit ((fun v => χ.toFun (fun i => f i v) j) u)
          ((fun v => χ.toFun (fun i => f i v) j) v)
        ≤ ∑ i, sepBit (f i u) (f i v) := by
    intro u v _
    exact χ.contract (fun i => f i u) (fun i => f i v)
  calc ∑ j, entropy M (B j)
      ≤ ∑ j, cutWeight M.toBulkGraph (fun v => χ.toFun (fun i => f i v) j) :=
        Finset.sum_le_sum (fun j _ => hle j)
    _ ≤ ∑ i, cutWeight M.toBulkGraph (f i) := hcomb f _ hcontract
    _ = ∑ i, entropy M (A i) := Finset.sum_congr rfl (fun i _ => (hfe i).symm)
