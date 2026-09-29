-- Prove2me | solution 2 for SheafCohomologyRobustness.NerveBetti.finrank_nerveH1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:28:05.664649+00:00
-- url     : https://prove2.me/submissions/ce63d855-5f78-4813-b97e-a2b67224167a

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
open Finset SheafCohomologyRobustness NerveBetti GraphNerve in
theorem solution {ι Edge : Type*} (G : NerveGraph ι Edge) [Fintype ι] [Fintype Edge] [Nonempty ι]
    (hconn : IsConnectedNerve (edgeAdj G)) :
    (Module.finrank ℝ ((Edge → ℝ) ⧸ LinearMap.range (delta G)) : ℤ)
      = (Fintype.card Edge : ℤ) - (Fintype.card ι : ℤ) + 1 := by
  -- the kernel of `δ` is the line of constants
  have hker : LinearMap.ker (delta G) = Submodule.span ℝ {(fun _ => 1 : ι → ℝ)} := by
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
  have hne : (fun _ => 1 : ι → ℝ) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary ι)
    simp at this
  have hk : Module.finrank ℝ (LinearMap.ker (delta G)) = 1 := by
    rw [hker]
    exact finrank_span_singleton hne
  -- rank–nullity for `δ : ℝ^ι → ℝ^Edge`
  have h2 := LinearMap.finrank_range_add_finrank_ker (delta G)
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (delta G))
  rw [Module.finrank_fintype_fun_eq_card] at h1
  omega
