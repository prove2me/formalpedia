-- Prove2me | solution 1 for KServer.slow_decrement_of_doob_jump
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:14:32.239227+00:00
-- url     : https://prove2.me/submissions/f4cd8237-8368-41e1-a091-6046940f2a62

import Mathlib
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_slow_decrement_cond

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- The past mass advances by exactly the size of the chunk being revealed. -/
theorem pastSize_succ (h : ℕ) (ω : C.Ω) :
    C.pastSize (h + 1) ω
      = C.pastSize h ω + ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => (i : ℕ) = h),
          C.size ω i := by
  unfold ChunkSystemB.pastSize
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  · refine Finset.disjoint_filter.mpr ?_
    intro i _ hlt heq
    omega

/-- One step of the past mass is at most the size ceiling. -/
theorem pastSize_step_le (hcHi : 0 ≤ cHi) (h : ℕ) (ω : C.Ω) :
    C.pastSize (h + 1) ω - C.pastSize h ω ≤ cHi := by
  rw [pastSize_succ]
  have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => (i : ℕ) = h), C.size ω i ≤ cHi := by
    rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter (fun i : Fin C.m => (i : ℕ) = h)) with he | ⟨y, hy⟩
    · rw [he]; simpa using hcHi
    · have hsingle : Finset.univ.filter (fun i : Fin C.m => (i : ℕ) = h) = {y} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hy, fun z hz => ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hy
        exact Fin.ext (hz.trans hy.symm)
      rw [hsingle, Finset.sum_singleton]
      exact (C.hsize ω y).2
  linarith

end ChunkSystemB

end KServer

open KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) {jb : ℝ}
    (hjb : C.DoobJumpBound jb) (hcHi : 0 ≤ cHi) :
    C.SlowDecrementC (cHi + jb) := by
  intro h ω
  have hd := C.doobTotal_eq_past_add_condFuture h ω
  have hd1 := C.doobTotal_eq_past_add_condFuture (h + 1) ω
  have hjump : C.doobTotal h ω - C.doobTotal (h + 1) ω ≤ jb := by
    have hb := hjb h ω
    rw [abs_le] at hb
    linarith [hb.1]
  have hpast : C.pastSize (h + 1) ω - C.pastSize h ω ≤ cHi :=
    KServer.ChunkSystemB.pastSize_step_le hcHi h ω
  linarith
