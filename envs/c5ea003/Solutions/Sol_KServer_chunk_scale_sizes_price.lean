-- Prove2me | solution 1 for KServer.chunk_scale_sizes_price
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T02:13:18.360629+00:00
-- url     : https://prove2.me/submissions/28b804b2-5dca-423a-8d61-750600ad51f4

import Definitions.Def_KServer_chunk_cond

open KServer

private theorem costOn_nonneg {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h χ : List (Set X)) : 0 ≤ E.costOn h χ := by
  have hmono : E.cost h ≤ E.cost (h ++ χ) := by
    unfold EvaderAlgorithm.cost
    calc
      ∑ j ∈ Finset.range h.length,
          dist (E.pos (h.take j)) (E.pos (h.take (j + 1)))
        = ∑ j ∈ Finset.range h.length,
          dist (E.pos ((h ++ χ).take j)) (E.pos ((h ++ χ).take (j + 1))) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            have hj' := Finset.mem_range.mp hj
            rw [List.take_append_of_le_length (by omega : j ≤ h.length),
              List.take_append_of_le_length (by omega : j + 1 ≤ h.length)]
      _ ≤ ∑ j ∈ Finset.range (h ++ χ).length,
          dist (E.pos ((h ++ χ).take j)) (E.pos ((h ++ χ).take (j + 1))) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · apply Finset.range_mono; simp
            · intro j _ _; exact dist_nonneg
  exact sub_nonneg.mpr hmono

private theorem scaled_bailCost_le {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (h χ : List (Set X))
    (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * E.bailCost bail h χ p ≤ E.bailCost bail h χ (q * p) := by
  unfold EvaderAlgorithm.bailCost
  cases hq : bailTime bail h χ with
  | none => nlinarith [costOn_nonneg E h χ]
  | some q => nlinarith [costOn_nonneg E h (χ.take q)]

private noncomputable def scaledSystem {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ChunkSystemB X s t 0 (q * cB) (q * T) (q * pe) mL := by
  classical
  exact { C with
    size := fun ω i => q * C.size ω i
    hsmeas := by
      intro i ω ω' hh
      rw [C.hsmeas i ω ω' hh]
    hsize := fun ω i => ⟨mul_nonneg hq0 (C.hsize ω i).1,
      mul_le_mul_of_nonneg_left (C.hsize ω i).2 hq0⟩
    hcost := by
      intro i ω₀ E bail
      have h := mul_le_mul_of_nonneg_left (C.hcost i ω₀ E bail) hq0
      calc
        (q * C.size ω₀ i) * (∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀), C.P ω)
          = q * (C.size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀), C.P ω)) := by ring
        _ ≤ q * (∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀),
            C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten) (C.chunk ω i) pe) := h
        _ = ∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀),
            C.P ω * (q * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten) (C.chunk ω i) pe) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          ring
        _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀),
            C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten) (C.chunk ω i) (q * pe) := by
          apply Finset.sum_le_sum
          intro ω _
          exact mul_le_mul_of_nonneg_left
            (scaled_bailCost_le E bail _ _ pe q hq0 hq1) (C.hP ω).le
    htotal := by
      have h := mul_le_mul_of_nonneg_left C.htotal hq0
      convert h using 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← Finset.mul_sum]
      ring }

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∃ C' : ChunkSystemB X s t 0 (q * cB) (q * T) (q * pe) mL,
      C'.m = C.m ∧
      (∑ ω, C'.P ω * ∑ i, C'.size ω i) = q * (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
      ((∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) →
        ∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.DoobJumpBound (q * jb) := by
  classical
  let C' := scaledSystem C q hq0 hq1
  have hdoob (h : ℕ) (ω : C.Ω) : C'.doobTotal h ω = q * C.doobTotal h ω := by
    change (∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i, q * C.size ω' i) / C.mass (C.atom h ω)
      = q * ((∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i, C.size ω' i) / C.mass (C.atom h ω))
    have hnum : (∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i, q * C.size ω' i)
        = q * (∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i, C.size ω' i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [hnum]
    ring
  refine ⟨C', rfl, ?_, fun h => h, fun h => h, ?_⟩
  · change (∑ ω, C.P ω * ∑ i, q * C.size ω i) = q * (∑ ω, C.P ω * ∑ i, C.size ω i)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← Finset.mul_sum]
    ring
  · intro h ω
    rw [hdoob, hdoob, ← mul_sub, abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left (hjb h ω) hq0
