-- Prove2me | solution 1 for KServer.finite_chunk_certificate_iff
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T02:37:22.905994+00:00
-- url     : https://prove2.me/submissions/15a9926d-b44f-44d9-8e74-6b287b109a2d

import Definitions.Def_KServer_finite_chunk_certificates

open KServer

private theorem restricted_pos {X : Type*} [MetricSpace X] (E : EvaderAlgorithm X)
    (H : ℕ) (l : List (Set X)) (hl : l.length ≤ H) :
    (E.restrict H).extend.pos l = E.pos l := by
  simp [FiniteEvader.extend, EvaderAlgorithm.restrict, hl]

private theorem restricted_cost {X : Type*} [MetricSpace X] (E : EvaderAlgorithm X)
    (H : ℕ) (l : List (Set X)) (hl : l.length ≤ H) :
    (E.restrict H).extend.cost l = E.cost l := by
  unfold EvaderAlgorithm.cost
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [restricted_pos E H _ (by simpa using (min_le_right j l.length).trans hl),
    restricted_pos E H _ (by simpa using (min_le_right (j + 1) l.length).trans hl)]

private theorem restricted_costOn {X : Type*} [MetricSpace X] (E : EvaderAlgorithm X)
    (H : ℕ) (h χ : List (Set X)) (hH : (h ++ χ).length ≤ H) :
    (E.restrict H).extend.costOn h χ = E.costOn h χ := by
  unfold EvaderAlgorithm.costOn
  rw [restricted_cost E H _ hH, restricted_cost E H h (by simp only [List.length_append] at hH; omega)]

private theorem restricted_bailCost {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (b : List (Set X) → Bool)
    (H : ℕ) (h χ : List (Set X)) (p : ℝ) (hH : (h ++ χ).length ≤ H) :
    (E.restrict H).extend.bailCost (extendBail (fun l : BoundedHistory X H => b l.val)) h χ p
      = E.bailCost b h χ p := by
  have hprefix (q : ℕ) : (h ++ χ.take q).length ≤ H := by
    simp only [List.length_append, List.length_take] at *
    have := min_le_right q χ.length
    omega
  have hbail (q : ℕ) : extendBail (fun l : BoundedHistory X H => b l.val) (h ++ χ.take q)
      = b (h ++ χ.take q) := by
    unfold extendBail
    rw [dif_pos (hprefix q)]
  have htime : bailTime (extendBail (fun l : BoundedHistory X H => b l.val)) h χ
      = bailTime b h χ := by
    unfold bailTime
    congr 1
    funext q
    exact hbail q
  unfold EvaderAlgorithm.bailCost
  rw [htime]
  cases bailTime b h χ with
  | none => exact restricted_costOn E H h χ hH
  | some q => exact congrArg (fun z : ℝ => z + p) (restricted_costOn E H h (χ.take q) (hprefix q))

private theorem chunk_horizon {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi T p : ℝ} {mLo : ℕ}
    (C : FiniteChunkSystemB X s t cLo cHi T p mLo) (ω : C.Ω) (i : Fin C.m) :
    ((((List.ofFn (C.chunk ω)).take i).flatten) ++ C.chunk ω i).length ≤ C.H := by
  have hi : i.val < (List.ofFn (C.chunk ω)).length := by simpa using i.isLt
  have htake := List.take_succ_eq_append_getElem hi
  have heq : ((List.ofFn (C.chunk ω)).take (i.val + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take i.val).flatten ++ C.chunk ω i := by
    rw [htake]
    simp
  rw [← heq]
  exact ((List.take_prefix (i.val + 1) (List.ofFn (C.chunk ω))).flatten.length_le).trans (C.hH ω)

private theorem finite_sound {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi T p : ℝ} {mLo : ℕ}
    (C : FiniteChunkSystemB X s t cLo cHi T p mLo) :
    ∃ D : ChunkSystemB X s t cLo cHi T p mLo,
      D.m = C.m ∧
      ((∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) →
        ∀ ω₁ ω₂ : D.Ω, D.hist 0 ω₁ = D.hist 0 ω₂) := by
  classical
  let D : ChunkSystemB X s t cLo cHi T p mLo := {
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := C.m
    hist := C.hist
    chunk := C.chunk
    size := C.size
    hP := C.hP
    hPsum := C.hPsum
    hm := C.hm
    hm0 := C.hm0
    href := C.href
    hadapt := C.hadapt
    hsmeas := C.hsmeas
    hne := C.hne
    hlast := C.hlast
    hopt := C.hopt
    hsize := C.hsize
    htotal := C.htotal
    hcost := by
      intro i ω₀ E b
      have h := C.hcost i ω₀ (E.restrict C.H) (fun l => b l.val)
      convert h using 1
      apply Finset.sum_congr rfl
      intro ω _
      rw [restricted_bailCost E b C.H _ _ p (chunk_horizon C ω i)] }
  exact ⟨D, rfl, fun h => h⟩


/-- On a finite space, all universal online cost tests can be replaced exactly
by bounded finite tables of positions and bailout decisions. -/
theorem solution {X : Type*} [MetricSpace X] [Finite X] {s t : X}
    {cLo cHi T p : ℝ} {mLo : ℕ} :
    (∃ C : FiniteChunkSystemB X s t cLo cHi T p mLo,
      ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ↔
    (∃ D : ChunkSystemB X s t cLo cHi T p mLo,
      ∀ ω₁ ω₂ : D.Ω, D.hist 0 ω₁ = D.hist 0 ω₂) := by
  classical
  constructor
  · rintro ⟨C, h0⟩
    obtain ⟨D, _, hD⟩ := finite_sound C
    exact ⟨D, hD h0⟩
  · rintro ⟨D, h0⟩
    let H : ℕ := Finset.univ.sup (fun ω : D.Ω => ((List.ofFn (D.chunk ω)).flatten).length)
    let C : FiniteChunkSystemB X s t cLo cHi T p mLo := {
      Ω := D.Ω
      instFin := D.instFin
      instDec := D.instDec
      P := D.P
      m := D.m
      H := H
      hist := D.hist
      chunk := D.chunk
      size := D.size
      hP := D.hP
      hPsum := D.hPsum
      hm := D.hm
      hm0 := D.hm0
      href := D.href
      hadapt := D.hadapt
      hsmeas := D.hsmeas
      hne := D.hne
      hlast := D.hlast
      hopt := D.hopt
      hsize := D.hsize
      htotal := D.htotal
      hH := by
        intro ω
        change ((List.ofFn (D.chunk ω)).flatten).length ≤
          Finset.univ.sup (fun ω : D.Ω => ((List.ofFn (D.chunk ω)).flatten).length)
        exact Finset.le_sup (f := fun ω : D.Ω => ((List.ofFn (D.chunk ω)).flatten).length)
          (Finset.mem_univ ω)
      hcost := fun i ω₀ A b => D.hcost i ω₀ A.extend (extendBail b) }
    exact ⟨C, h0⟩
