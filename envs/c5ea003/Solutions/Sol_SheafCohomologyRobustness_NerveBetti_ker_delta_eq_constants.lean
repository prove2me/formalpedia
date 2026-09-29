-- Prove2me | solution 1 for SheafCohomologyRobustness.NerveBetti.ker_delta_eq_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:37:34.898967+00:00
-- url     : https://prove2.me/submissions/75186403-540b-4311-8a40-6594fdf7f883

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
open Finset SheafCohomologyRobustness NerveBetti GraphNerve in
theorem solution {ι Edge : Type*} (G : NerveGraph ι Edge) [Nonempty ι]
    (hconn : IsConnectedNerve (edgeAdj G)) :
    LinearMap.ker (delta G) = Submodule.span ℝ {(fun _ => 1 : ι → ℝ)} := by
  -- a function with no discrepancy across overlaps is constant along walks
  have hwalk : ∀ f : ι → ℝ, (∀ e : Edge, f (G.tgt e) = f (G.src e)) →
      ∀ (i : ι) (l : List ι), IsWalk (edgeAdj G) i l → f (endpt i l) = f i := by
    intro f hf i l
    induction l generalizing i with
    | nil => intro _; rfl
    | cons j t ih =>
      rintro ⟨hij, ht⟩
      have hstep : f j = f i := by
        obtain ⟨e, ⟨hs, ht'⟩ | ⟨hs, ht'⟩⟩ := hij
        · rw [← ht', ← hs]; exact hf e
        · rw [← ht', ← hs]; exact (hf e).symm
      show f (endpt j t) = f i
      rw [ih j ht, hstep]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hf
    have hf' : ∀ e : Edge, f (G.tgt e) = f (G.src e) := fun e =>
      sub_eq_zero.mp (congrFun hf e)
    -- connectedness: every region is reached from `i₀`, so `f` is the constant `f i₀`
    refine ⟨f i₀, funext fun j => ?_⟩
    obtain ⟨l, hl, hend⟩ := hconn i₀ j
    have := hwalk f hf' i₀ l hl
    rw [hend] at this
    simp [this]
  · rintro ⟨a, rfl⟩
    funext e
    show (a • fun _ : ι => (1 : ℝ)) (G.tgt e) - (a • fun _ : ι => (1 : ℝ)) (G.src e) = 0
    simp
