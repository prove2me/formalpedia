-- Prove2me | solution 1 for KServer.nonneg_chunk_positive_support
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:23:17.423993+00:00
-- url     : https://prove2.me/submissions/93a5e26e-929f-4cb3-a897-fd8ebc8a6ae2

import Definitions.Def_KServer_nonneg_chunk_system

set_option autoImplicit false
open KServer
open scoped BigOperators

private theorem sum_positive_support {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    [DecidablePred (fun ω => 0 < P ω)] (hP : ∀ ω, 0 ≤ P ω) (f : Ω → ℝ) :
    (∑ ω : {ω : Ω // 0 < P ω}, P ω.val * f ω.val) = ∑ ω, P ω * f ω := by
  classical
  calc
    _ = ∑ ω ∈ Finset.univ.filter (fun ω => 0 < P ω), P ω * f ω := by
      exact (Finset.sum_subtype _ (by simp) (fun ω => P ω * f ω)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro ω _ hn
      have hn' : ¬ 0 < P ω := by simpa using hn
      have hz : P ω = 0 := le_antisymm (le_of_not_gt hn') (hP ω)
      simp [hz]

private theorem sum_filter_positive_support {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    [DecidablePred (fun ω => 0 < P ω)] (hP : ∀ ω, 0 ≤ P ω)
    (r : Ω → Prop) [DecidablePred r] (f : Ω → ℝ) :
    (∑ ω ∈ (Finset.univ : Finset {ω : Ω // 0 < P ω}).filter (fun ω => r ω.val),
      P ω.val * f ω.val) = ∑ ω ∈ Finset.univ.filter r, P ω * f ω := by
  classical
  simp only [Finset.sum_filter]
  simpa only [mul_ite, mul_zero] using
    sum_positive_support P hP (fun ω => if r ω then f ω else 0)

private theorem mass_filter_positive_support {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    [DecidablePred (fun ω => 0 < P ω)] (hP : ∀ ω, 0 ≤ P ω)
    (r : Ω → Prop) [DecidablePred r] :
    (∑ ω ∈ (Finset.univ : Finset {ω : Ω // 0 < P ω}).filter (fun ω => r ω.val), P ω.val) =
      ∑ ω ∈ Finset.univ.filter r, P ω := by
  simpa only [mul_one] using sum_filter_positive_support P hP r (fun _ => 1)

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price jb : ℝ} {mLo : ℕ}
    (D : NonnegChunkSystemB X s t cLo cHi total price mLo)
    (h0 : ∀ ω ω' : D.Ω, D.hist 0 ω = D.hist 0 ω')
    (hch : ∀ (ω : D.Ω) (i : Fin D.m), D.chunk ω i ≠ [])
    (hjump : D.DoobJumpBound jb) :
    ∃ (C : ChunkSystemB X s t cLo cHi total price mLo) (e : C.Ω ↪ D.Ω),
      C.m = D.m ∧
      (∀ ω, C.P ω = D.P (e ω)) ∧
      (∀ f : D.Ω → ℝ, (∑ ω, C.P ω * f (e ω)) = ∑ ω, D.P ω * f ω) ∧
      (∀ h ω, C.hist h ω = D.hist h (e ω)) ∧
      (∑ ω, C.P ω * ∑ i, C.size ω i) = (∑ ω, D.P ω * ∑ i, D.size ω i) ∧
      (∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') ∧
      (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
      C.DoobJumpBound jb := by
  classical
  let C : ChunkSystemB X s t cLo cHi total price mLo := {
    Ω := {ω : D.Ω // 0 < D.P ω}
    instFin := inferInstance
    instDec := inferInstance
    P := fun ω => D.P ω.val
    m := D.m
    hist := fun h ω => D.hist h ω.val
    chunk := fun ω i => D.chunk ω.val i
    size := fun ω i => D.size ω.val i
    hP := fun ω => ω.property
    hPsum := by
      simpa only [mul_one] using (sum_positive_support D.P D.hP (fun _ => 1)).trans
        (by simpa only [mul_one] using D.hPsum)
    hm := D.hm
    hm0 := D.hm0
    href := fun i j hij ω ω' h => D.href i j hij ω.val ω'.val h
    hadapt := fun i ω ω' h => D.hadapt i ω.val ω'.val h
    hsmeas := fun i ω ω' h => D.hsmeas i ω.val ω'.val h
    hne := fun ω i => D.hne ω.val i
    hlast := fun ω => D.hlast ω.val
    hopt := fun ω => D.hopt ω.val
    hsize := fun ω i => D.hsize ω.val i
    hcost := by
      intro i ω₀ E bail
      rw [mass_filter_positive_support D.P D.hP
          (fun ω => D.hist i ω = D.hist i ω₀.val),
        sum_filter_positive_support D.P D.hP
          (fun ω => D.hist i ω = D.hist i ω₀.val)
          (fun ω => E.bailCost bail (((List.ofFn (D.chunk ω)).take i).flatten) (D.chunk ω i) price)]
      exact D.hcost i ω₀.val E bail
    htotal := by
      rw [sum_positive_support D.P D.hP (fun ω => ∑ i, D.size ω i)]
      exact D.htotal }
  have hdoob (h : ℕ) (ω : C.Ω) : C.doobTotal h ω = D.condTotal h ω.val := by
    change (∑ ω' ∈ (Finset.univ : Finset {ω : D.Ω // 0 < D.P ω}).filter (fun ω' => D.hist h ω'.val = D.hist h ω.val),
        D.P ω'.val * ∑ i, D.size ω'.val i) /
      (∑ ω' ∈ (Finset.univ : Finset {ω : D.Ω // 0 < D.P ω}).filter (fun ω' => D.hist h ω'.val = D.hist h ω.val), D.P ω'.val) = _
    rw [sum_filter_positive_support D.P D.hP
        (fun ω' => D.hist h ω' = D.hist h ω.val) (fun ω' => ∑ i, D.size ω' i),
      mass_filter_positive_support D.P D.hP (fun ω' => D.hist h ω' = D.hist h ω.val)]
    rfl
  refine ⟨C, ⟨Subtype.val, Subtype.val_injective⟩, rfl, (fun _ => rfl), ?_,
    (fun _ _ => rfl), ?_, (fun ω ω' => h0 ω.val ω'.val),
    (fun ω i => hch ω.val i), ?_⟩
  · intro f
    exact sum_positive_support D.P D.hP f
  · exact sum_positive_support D.P D.hP (fun ω => ∑ i, D.size ω i)
  · intro h ω
    rw [hdoob (h + 1) ω, hdoob h ω]
    exact hjump h ω.val ω.property
