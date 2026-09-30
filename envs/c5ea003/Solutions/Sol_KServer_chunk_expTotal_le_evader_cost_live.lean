-- Prove2me | solution 1 for KServer.chunk_expTotal_le_evader_cost_live
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T06:30:25.192362+00:00
-- url     : https://prove2.me/submissions/a8a4acbb-7a20-410a-b8a5-5842d087f30c

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

private def neverBail {X : Type*} : List (Set X) → Bool := fun _ => false

private theorem bailCost_never {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h χ : List (Set X)) (p : ℝ) :
    E.bailCost neverBail h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost
  have hn : bailTime neverBail h χ = none := by
    unfold bailTime
    rw [List.find?_eq_none]
    intro x _; simp [neverBail]
  rw [hn]

/-- The flattened prefix of length `i + 1` is the prefix of length `i` plus chunk `i`. -/
private theorem ofFn_take_flatten {X : Type*} {n : ℕ} (f : Fin n → List (Set X)) (i : Fin n) :
    ((List.ofFn f).take (i : ℕ)).flatten ++ f i
      = ((List.ofFn f).take ((i : ℕ) + 1)).flatten := by
  have hlt' : (i : ℕ) < (List.ofFn f).length := by
    rw [List.length_ofFn]; exact i.isLt
  have hget : (List.ofFn f)[(i : ℕ)] = f i :=
    List.getElem_ofFn (by rw [List.length_ofFn]; exact i.isLt)
  rw [List.take_succ_eq_append_getElem hlt', hget, List.flatten_concat]

/-- Telescoping over `Fin m`, reindexed onto `Finset.range m`. -/
private theorem fin_tele (g : ℕ → ℝ) : ∀ m : ℕ,
    (∑ i : Fin m, (g (i + 1) - g i)) = g m - g 0 := by
  intro m
  calc (∑ i : Fin m, (g (i + 1) - g i)) = ∑ k ∈ Finset.range m, (g (k + 1) - g k) := by
        refine Finset.sum_bij (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (i : ℕ)) ?_ ?_ ?_ ?_
        · intro i _; rw [Finset.mem_range]; exact i.isLt
        · intro a _ b _ h; exact Fin.ext h
        · intro b hb; exact ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
        · intro i _; rfl
    _ = g m - g 0 := Finset.sum_range_sub g m

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (E : EvaderAlgorithm X) :
    (∑ ω, C.P ω * ∑ i, C.size ω i) ≤
      ∑ ω, C.P ω * E.cost (C.seq ω) := by
  classical
  set chOn : C.Ω → Fin C.m → ℝ := fun w i =>
    E.costOn (((List.ofFn (C.chunk w)).take (i : ℕ)).flatten) (C.chunk w i) with hchOn
  have hfib : ∀ (i : Fin C.m) (w0 : C.Ω),
      C.size w0 i * (∑ w ∈ (Finset.univ : Finset C.Ω).filter (fun w => C.hist i w = C.hist i w0), C.P w)
        ≤ ∑ w ∈ (Finset.univ : Finset C.Ω).filter (fun w => C.hist i w = C.hist i w0), C.P w * chOn w i := by
    intro i w0
    have h := C.hcost i w0 E neverBail
    rwa [show (fun w => C.P w * E.bailCost neverBail (((List.ofFn (C.chunk w)).take (i : ℕ)).flatten)
          (C.chunk w i) price) = (fun w => C.P w * chOn w i) by
      funext w; rw [hchOn, bailCost_never]] at h
  have hstep1 : ∀ (i : Fin C.m),
      (∑ w, C.P w * C.size w i) ≤ ∑ w, C.P w * chOn w i := by
    intro i
    set A : Finset ℕ := (Finset.univ : Finset C.Ω).image (fun w => C.hist i w) with hA
    have hmaps : ∀ w ∈ (Finset.univ : Finset C.Ω), C.hist i w ∈ A := by
      intro w hw; rw [hA]; exact Finset.mem_image_of_mem _ hw
    have decomp : ∀ (g : C.Ω → ℝ),
        (∑ w, C.P w * g w)
          = ∑ a ∈ A, ∑ w ∈ (Finset.univ : Finset C.Ω).filter
              (fun w => C.hist i w = a), C.P w * g w := by
      intro g; symm
      exact Finset.sum_fiberwise_of_maps_to hmaps fun w => C.P w * g w
    rw [decomp (fun w => C.size w i), decomp (fun w => chOn w i)]
    refine Finset.sum_le_sum fun a ha => ?_
    set Fib : Finset C.Ω := (Finset.univ : Finset C.Ω).filter (fun w => C.hist i w = a) with hFib
    by_cases hne : Fib = ∅
    · rw [hne]; simp
    · have hne' : Fib.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨w0, hw0⟩ := hne'
      have hw0' : C.hist i w0 = a := (Finset.mem_filter.mp hw0).2
      have hfeq : Fib = (Finset.univ : Finset C.Ω).filter
              (fun w => C.hist i w = C.hist i w0) :=
        Finset.filter_congr fun w _ =>
          ⟨fun h => by rw [h, hw0'], fun h => by rw [h, ← hw0']⟩
      have hsize : (∑ w ∈ Fib, C.P w * C.size w i) = ∑ w ∈ Fib, C.size w0 i * C.P w := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [C.hsmeas i w w0 (by rw [(Finset.mem_filter.mp hw).2, hw0']), mul_comm]
      have hsum : (∑ w ∈ Fib, C.size w0 i * C.P w) = (∑ w ∈ Fib, C.P w) * C.size w0 i :=
        (Finset.mul_sum Fib (fun w => C.P w) (C.size w0 i)).symm.trans (mul_comm _ _)
      have hb := hfib i w0
      rw [hfeq.symm] at hb
      rw [hsize, hsum, mul_comm]
      exact hb
  calc (∑ ω, C.P ω * ∑ i, C.size ω i)
      = ∑ i, ∑ ω, C.P ω * C.size ω i := by
        rw [show (∑ ω, C.P ω * (∑ i, C.size ω i)) = ∑ ω, ∑ i, C.P ω * C.size ω i from
          Fintype.sum_congr _ _ fun ω => Finset.mul_sum _ _ _]
        exact Finset.sum_comm
    _ ≤ ∑ i, ∑ ω, C.P ω * chOn ω i := Finset.sum_le_sum fun i _ => hstep1 i
    _ = ∑ ω, C.P ω * ∑ i, chOn ω i := by
        rw [Finset.sum_comm, show (∑ ω, ∑ i, C.P ω * chOn ω i)
          = ∑ ω, C.P ω * (∑ i, chOn ω i) from
          Fintype.sum_congr _ _ fun ω => (Finset.mul_sum _ _ _).symm]
    _ = ∑ ω, C.P ω * E.cost (C.seq ω) := by
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      set g : ℕ → ℝ := fun k => E.cost ((List.ofFn (C.chunk ω)).take k).flatten
      have hstep : ∀ (i : Fin C.m), g (i + 1) - g i
          = E.costOn (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i) := by
        intro i
        unfold g
        rw [← ofFn_take_flatten (C.chunk ω) i]
        unfold EvaderAlgorithm.costOn EvaderAlgorithm.cost
        rfl
      have h0 : g 0 = 0 := by
        unfold g EvaderAlgorithm.cost
        simp [List.take_zero, List.flatten_nil]
      have hsum : (∑ i, chOn ω i) = g C.m - g 0 := by
        rw [← fin_tele, hchOn]; exact Finset.sum_congr rfl fun i _ => (hstep i).symm
      rw [hsum, h0, sub_zero]
      show C.P ω * E.cost ((List.ofFn (C.chunk ω)).take C.m).flatten
        = C.P ω * E.cost (C.seq ω)
      have htake : ((List.ofFn (C.chunk ω)).take C.m).flatten = C.seq ω := by
        calc ((List.ofFn (C.chunk ω)).take C.m).flatten
            = ((List.ofFn (C.chunk ω)).take (List.ofFn (C.chunk ω)).length).flatten := by
              rw [List.length_ofFn]
          _ = (List.ofFn (C.chunk ω)).flatten := by rw [List.take_length]
          _ = C.seq ω := rfl
      rw [htake]
