-- Prove2me | solution 1 for KServer.online_cost_compactness
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:10:57.207711+00:00
-- url     : https://prove2.me/submissions/9ddcc411-953b-4181-b0cc-033cfad1d799

import Theorems.Thm_KServer_exists_lazy_algorithm
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open KServer

private theorem lazy_reachable {k : ℕ} {M : Type} [MetricSpace M]
    (B : OnlineAlgorithm k M)
    (hB : ∀ (l : List M) (r : M), ∃ i : Fin k,
      B.conf (l ++ [r]) = Function.update (B.conf l) i r)
    (l : List M) (i : Fin k) :
    B.conf l i ∈ Set.range (B.conf []) ∨ B.conf l i ∈ l := by
  classical
  induction l using List.reverseRecOn with
  | nil => exact Or.inl ⟨i, rfl⟩
  | append_singleton l r ih =>
    obtain ⟨j, hj⟩ := hB l r
    rw [hj]
    by_cases hij : i = j
    · subst i
      simp
    · rw [Function.update_of_ne hij]
      rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)

/-- Compactness for arbitrary prescribed pointwise cost bounds. -/
theorem solution (k : ℕ) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (b : List M → ℝ)
    (h : ∀ F : Finset (List M), ∃ A : OnlineAlgorithm k M,
      A.conf [] = C₀ ∧ ∀ σ ∈ F, A.cost σ ≤ b σ) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
      ∀ σ : List M, A.cost σ ≤ b σ := by
  classical
  let R (l : List M) := {x : M // x ∈ Set.range C₀ ∨ x ∈ l}
  have hfinite (l : List M) : (Set.range C₀ ∪ {x : M | x ∈ l}).Finite :=
    (Set.finite_range C₀).union l.finite_toSet
  letI (l : List M) : Fintype (R l) := (hfinite l).fintype
  let Q := ∀ l : List M, Fin k → R l
  let decode (q : Q) (l : List M) (i : Fin k) : M := (q l i).val
  let cost (q : Q) (σ : List M) : ℝ :=
    ∑ j ∈ Finset.range σ.length,
      moveCost (decode q (σ.take j)) (decode q (σ.take (j + 1)))
  have hcont (l : List M) (i : Fin k) : Continuous (fun q : Q => decode q l i) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply l))
  have hcost (σ : List M) : Continuous (fun q : Q => cost q σ) := by
    apply continuous_finsetSum
    intro j hj
    apply continuous_finsetSum
    intro i hi
    exact (hcont _ _).dist (hcont _ _)
  let G (σ : List M) : Set Q := {q |
    (∀ i, decode q [] i = C₀ i) ∧
    (∀ (l : List M) (r : M), ∃ i, decode q (l ++ [r]) i = r) ∧
    cost q σ ≤ b σ}
  have hclosed (σ : List M) : IsClosed (G σ) := by
    apply IsClosed.inter
    · simpa only [Set.iInter_setOf] using
        (isClosed_iInter (fun i => isClosed_eq (hcont [] i)
          (continuous_const (y := C₀ i))))
    · apply IsClosed.inter
      · simpa only [Set.iInter_setOf, Set.iUnion_setOf] using
          (isClosed_iInter (fun l => isClosed_iInter (fun r =>
            isClosed_iUnion_of_finite (fun i : Fin k =>
              isClosed_eq (hcont (l ++ [r]) i) (continuous_const (y := r))))))
      · exact isClosed_le (hcost σ) continuous_const
  have hmeet (F : Finset (List M)) : (⋂ σ ∈ F, G σ).Nonempty := by
    obtain ⟨A, hA0, hA⟩ := h F
    obtain ⟨B, hB0, hBA, hB⟩ := KServer.exists_lazy_algorithm k M A
    have hBC : B.conf [] = C₀ := hB0.trans hA0
    let q : Q := fun l i => ⟨B.conf l i, by
      have hr := lazy_reachable B hB l i
      rwa [hBC] at hr⟩
    refine ⟨q, ?_⟩
    simp only [Set.mem_iInter]
    intro σ hσ
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact congrFun hBC i
    · exact B.serves
    · exact (hBA σ).trans (hA σ hσ)
  obtain ⟨q, hq⟩ := CompactSpace.iInter_nonempty hclosed hmeet
  have hq' (σ : List M) : q ∈ G σ := Set.mem_iInter.mp hq σ
  let A : OnlineAlgorithm k M :=
    { conf := decode q
      serves := (hq' []).2.1 }
  refine ⟨A, funext (hq' []).1, ?_⟩
  intro σ
  exact (hq' σ).2.2

#print axioms solution
