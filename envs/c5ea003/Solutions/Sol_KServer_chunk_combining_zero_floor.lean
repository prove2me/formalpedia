-- Prove2me | solution 1 for KServer.chunk_combining_zero_floor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T09:47:12.913401+00:00
-- url     : https://prove2.me/submissions/918800fc-7c64-4160-b8f4-9fba2e7ae74b

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_bail_append

/-! ### Pasted verbatim: platform Definitions module Def_KServer_chunk_stopping (not on local disk). -/

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- The chunk size indexed by a natural number, zero beyond the last chunk. -/
noncomputable def sizeN (h : ℕ) (ω : C.Ω) : ℝ :=
  if hh : h < C.m then C.size ω ⟨h, hh⟩ else 0

theorem sizeN_congr {h : ℕ} {ω ω' : C.Ω} (hh : C.hist h ω' = C.hist h ω) :
    C.sizeN h ω' = C.sizeN h ω := by
  unfold sizeN
  by_cases hm : h < C.m
  · rw [dif_pos hm, dif_pos hm]
    exact C.hsmeas ⟨h, hm⟩ ω' ω hh
  · rw [dif_neg hm, dif_neg hm]

theorem sizeN_le {h : ℕ} (hm : h < C.m) (ω : C.Ω) : C.sizeN h ω ≤ cHi := by
  unfold sizeN
  rw [dif_pos hm]
  exact (C.hsize ω ⟨h, hm⟩).2

theorem le_sizeN {h : ℕ} (hm : h < C.m) (ω : C.Ω) : cLo ≤ C.sizeN h ω := by
  unfold sizeN
  rw [dif_pos hm]
  exact (C.hsize ω ⟨h, hm⟩).1

theorem sizeN_nonneg (hcLo : 0 ≤ cLo) (h : ℕ) (ω : C.Ω) : 0 ≤ C.sizeN h ω := by
  unfold sizeN
  by_cases hm : h < C.m
  · rw [dif_pos hm]
    exact le_trans hcLo (C.hsize ω ⟨h, hm⟩).1
  · rw [dif_neg hm]

/-- Peeling one chunk off the future mass. -/
theorem futureSize_succ (h : ℕ) (ω : C.Ω) :
    C.futureSize h ω = C.sizeN h ω + C.futureSize (h + 1) ω := by
  unfold futureSize sizeN
  by_cases hh : h < C.m
  · rw [dif_pos hh]
    have hins : Finset.univ.filter (fun i : Fin C.m => h ≤ i.val)
        = insert (⟨h, hh⟩ : Fin C.m)
            (Finset.univ.filter (fun i : Fin C.m => h + 1 ≤ i.val)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rcases Nat.eq_or_lt_of_le hi with he | hl
        · left
          exact Fin.ext he.symm
        · right
          omega
      · rintro (rfl | hi)
        · exact le_refl _
        · omega
    rw [hins, Finset.sum_insert (by simp)]
  · rw [dif_neg hh]
    have h1 : Finset.univ.filter (fun i : Fin C.m => h ≤ i.val) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i _ => by have := i.2; omega)
    have h2 : Finset.univ.filter (fun i : Fin C.m => h + 1 ≤ i.val) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i _ => by have := i.2; omega)
    rw [h1, h2]
    simp

theorem futureSize_of_m_le {h : ℕ} (hm : C.m ≤ h) (ω : C.Ω) :
    C.futureSize h ω = 0 := by
  unfold futureSize
  have h1 : Finset.univ.filter (fun i : Fin C.m => h ≤ i.val) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun i _ => by have := i.2; omega)
  rw [h1]
  rfl

theorem futureSize_nonneg (hcLo : 0 ≤ cLo) (h : ℕ) (ω : C.Ω) :
    0 ≤ C.futureSize h ω :=
  Finset.sum_nonneg fun i _ => le_trans hcLo (C.hsize ω i).1

theorem le_futureSize (hcLo : 0 ≤ cLo) {h : ℕ} (hm : h < C.m) (ω : C.Ω) :
    cLo ≤ C.futureSize h ω :=
  le_trans (C.hsize ω ⟨h, hm⟩).1
    (Finset.single_le_sum (fun i _ => le_trans hcLo (C.hsize ω i).1)
      (by simp [Finset.mem_filter]))

/-- Peeling one chunk onto the past mass. -/
theorem pastSize_succ (h : ℕ) (ω : C.Ω) :
    C.pastSize (h + 1) ω = C.pastSize h ω + C.sizeN h ω := by
  unfold pastSize sizeN
  by_cases hh : h < C.m
  · rw [dif_pos hh]
    have hins : Finset.univ.filter (fun i : Fin C.m => i.val < h + 1)
        = insert (⟨h, hh⟩ : Fin C.m)
            (Finset.univ.filter (fun i : Fin C.m => i.val < h)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with he | hl
        · left
          exact Fin.ext he
        · right
          omega
      · rintro (rfl | hi)
        · show h < h + 1
          omega
        · omega
    rw [hins, Finset.sum_insert (by simp), add_comm]
  · rw [dif_neg hh]
    have hset : Finset.univ.filter (fun i : Fin C.m => i.val < h + 1)
        = Finset.univ.filter (fun i : Fin C.m => i.val < h) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := i.2
      omega
    rw [hset, add_zero]

theorem condExp_sub (f g : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (fun ω' => f ω' - g ω') h ω = C.condExp f h ω - C.condExp g h ω := by
  unfold condExp
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  show C.P ω' * (f ω' - g ω') = _
  ring

theorem condFuture_congr {h : ℕ} {ω ω' : C.Ω} (hh : C.hist h ω' = C.hist h ω) :
    C.condFuture h ω' = C.condFuture h ω :=
  C.condExp_congr _ hh

theorem condFuture_nonneg (hcLo : 0 ≤ cLo) (h : ℕ) (ω : C.Ω) :
    0 ≤ C.condFuture h ω :=
  C.le_condExp fun ω' _ => C.futureSize_nonneg hcLo h ω'

theorem condFuture_of_m_le {h : ℕ} (hm : C.m ≤ h) (ω : C.Ω) :
    C.condFuture h ω = 0 := by
  unfold condFuture
  rw [C.condExp_congr_fun (g := fun _ => (0:ℝ))
    (fun ω' _ => C.futureSize_of_m_le hm ω')]
  exact C.condExp_const 0 h ω

theorem lt_condFuture (hcLo : 0 < cLo) {h : ℕ} (hm : h < C.m) (ω : C.Ω) :
    0 < C.condFuture h ω :=
  lt_of_lt_of_le hcLo
    (C.le_condExp fun ω' _ => C.le_futureSize (le_of_lt hcLo) hm ω')

/-- The one-step **drift identity**: the conditional future mass is a
supermartingale with exact per-step drift the (predictable) current size. -/
theorem condFuture_succ_step (h : ℕ) (ω : C.Ω) :
    C.condExp (C.condFuture (h + 1)) h ω = C.condFuture h ω - C.sizeN h ω := by
  have h1 : C.condExp (C.condFuture (h + 1)) h ω
      = C.condExp (C.futureSize (h + 1)) h ω :=
    C.condExp_condExp (Nat.le_succ h) ω
  rw [h1]
  have h2 : C.condExp (C.futureSize (h + 1)) h ω
      = C.condExp (fun ω' => C.futureSize h ω' - C.sizeN h ω') h ω :=
    C.condExp_congr_fun fun ω' _ => by
      rw [C.futureSize_succ h ω']
      ring
  rw [h2, C.condExp_sub]
  congr 1
  rw [C.condExp_congr_fun (g := fun _ => C.sizeN h ω)
    (fun ω' hm => C.sizeN_congr (C.mem_atom.mp hm))]
  exact C.condExp_const _ h ω

/-- The jump of the conditional future mass around its predictable drift is
controlled by the Doob jump bound. -/
theorem condFuture_succ_sub {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (h : ℕ) (ω : C.Ω) :
    |C.condFuture (h + 1) ω - (C.condFuture h ω - C.sizeN h ω)| ≤ jbS := by
  have heq : C.doobTotal (h + 1) ω - C.doobTotal h ω
      = C.condFuture (h + 1) ω - (C.condFuture h ω - C.sizeN h ω) := by
    rw [C.doobTotal_eq_past_add_condFuture, C.doobTotal_eq_past_add_condFuture,
      C.pastSize_succ]
    ring
  rw [← heq]
  exact hjb h ω

theorem condFuture_succ_le {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (h : ℕ) (ω : C.Ω) :
    C.condFuture (h + 1) ω ≤ C.condFuture h ω - C.sizeN h ω + jbS := by
  have := (abs_le.mp (C.condFuture_succ_sub hjb h ω)).2
  linarith

theorem le_condFuture_succ {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (h : ℕ) (ω : C.Ω) :
    C.condFuture h ω - C.sizeN h ω - jbS ≤ C.condFuture (h + 1) ω := by
  have := (abs_le.mp (C.condFuture_succ_sub hjb h ω)).1
  linarith

/-- In the **descending regime** (`jbS ≤ cLo`) the conditional future mass is
pointwise non-increasing. -/
theorem condFuture_succ_le_self {jbS : ℝ} (hjb : C.DoobJumpBound jbS)
    (hjbLo : jbS ≤ cLo) (h : ℕ) (ω : C.Ω) :
    C.condFuture (h + 1) ω ≤ C.condFuture h ω := by
  by_cases hm : h < C.m
  · have h1 := C.condFuture_succ_le hjb h ω
    have h2 := C.le_sizeN hm ω
    linarith
  · rw [C.condFuture_of_m_le (by omega), C.condFuture_of_m_le (by omega)]

theorem condFuture_antitone {jbS : ℝ} (hjb : C.DoobJumpBound jbS)
    (hjbLo : jbS ≤ cLo) {h h' : ℕ} (hle : h ≤ h') (ω : C.Ω) :
    C.condFuture h' ω ≤ C.condFuture h ω := by
  induction h', hle using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    exact le_trans (C.condFuture_succ_le_self hjb hjbLo n ω) ih

/-- A **stopping time** for the chunk filtration: whether it has fired by
time `h` is determined by the time-`h` history. -/
def IsStopping (σ : C.Ω → ℕ) : Prop :=
  ∀ (h : ℕ) (ω ω' : C.Ω), C.hist h ω = C.hist h ω' → (σ ω ≤ h ↔ σ ω' ≤ h)

/-- The first time the conditional future mass drops to level `x`. -/
noncomputable def hitTime (x : ℝ) (ω : C.Ω) : ℕ :=
  sInf {h | C.condFuture h ω ≤ x}

theorem hitSet_nonempty {x : ℝ} (hx : 0 ≤ x) (ω : C.Ω) :
    {h | C.condFuture h ω ≤ x}.Nonempty :=
  ⟨C.m, by show C.condFuture C.m ω ≤ x; rw [C.condFuture_of_m_le (le_refl _)]; exact hx⟩

theorem condFuture_hitTime_le {x : ℝ} (hx : 0 ≤ x) (ω : C.Ω) :
    C.condFuture (C.hitTime x ω) ω ≤ x :=
  Nat.sInf_mem (C.hitSet_nonempty hx ω)

theorem hitTime_le_m {x : ℝ} (hx : 0 ≤ x) (ω : C.Ω) : C.hitTime x ω ≤ C.m :=
  Nat.sInf_le (by show C.condFuture C.m ω ≤ x
                  rw [C.condFuture_of_m_le (le_refl _)]; exact hx)

theorem lt_condFuture_of_lt_hitTime {x : ℝ} {h : ℕ} {ω : C.Ω}
    (hlt : h < C.hitTime x ω) : x < C.condFuture h ω := by
  by_contra hcon
  have hmem : h ∈ {h | C.condFuture h ω ≤ x} := by
    simpa using not_lt.mp hcon
  have hle : C.hitTime x ω ≤ h := Nat.sInf_le hmem
  omega

theorem hitTime_le_iff {x : ℝ} (hx : 0 ≤ x) (ω : C.Ω) (h : ℕ) :
    C.hitTime x ω ≤ h ↔ ∃ h' ≤ h, C.condFuture h' ω ≤ x := by
  constructor
  · intro hτ
    exact ⟨C.hitTime x ω, hτ, C.condFuture_hitTime_le hx ω⟩
  · rintro ⟨h', hh', hg⟩
    exact le_trans (Nat.sInf_le hg) hh'

theorem hitTime_isStopping {x : ℝ} (hx : 0 ≤ x) :
    C.IsStopping (C.hitTime x) := by
  intro h ω ω' hh
  have hg : ∀ h' ≤ h, C.condFuture h' ω' = C.condFuture h' ω := fun h' hh' =>
    C.condFuture_congr (C.href h' h hh' ω' ω hh.symm)
  rw [C.hitTime_le_iff hx, C.hitTime_le_iff hx]
  constructor
  · rintro ⟨h', hh', hgle⟩
    exact ⟨h', hh', by rw [hg h' hh']; exact hgle⟩
  · rintro ⟨h', hh', hgle⟩
    exact ⟨h', hh', by rw [← hg h' hh']; exact hgle⟩

/-- A stopping time that has fired is constant on the atoms of its own
stopping level. -/
theorem hitTime_congr {x : ℝ} (hx : 0 ≤ x) {h : ℕ} {ω ω' : C.Ω}
    (hh : C.hist h ω' = C.hist h ω) (hτ : C.hitTime x ω ≤ h) :
    C.hitTime x ω' = C.hitTime x ω := by
  have hg : ∀ h' ≤ h, C.condFuture h' ω' = C.condFuture h' ω := fun h' hh' =>
    C.condFuture_congr (C.href h' h hh' ω' ω hh)
  have hτ' : C.hitTime x ω' ≤ C.hitTime x ω := by
    rw [C.hitTime_le_iff hx]
    exact ⟨C.hitTime x ω, le_refl _,
      by rw [hg _ hτ]; exact C.condFuture_hitTime_le hx ω⟩
  rcases Nat.lt_or_ge (C.hitTime x ω') (C.hitTime x ω) with hlt | hge
  · exfalso
    have h1 : x < C.condFuture (C.hitTime x ω') ω :=
      C.lt_condFuture_of_lt_hitTime hlt
    have h2 : C.condFuture (C.hitTime x ω') ω' ≤ x :=
      C.condFuture_hitTime_le hx ω'
    rw [hg _ (le_trans (le_of_lt hlt) hτ)] at h2
    linarith
  · omega

/-- Summation engine: two functions whose `P`-weighted sums agree on every
time-`h` atom have equal `P`-weighted sums over every time-`h`-saturated set. -/
theorem sum_saturated (h : ℕ) (B : Finset C.Ω)
    (hsat : ∀ ω ∈ B, ∀ ω', C.hist h ω' = C.hist h ω → ω' ∈ B)
    (f g : C.Ω → ℝ)
    (hfg : ∀ ω ∈ B, ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      = ∑ ω' ∈ C.atom h ω, C.P ω' * g ω') :
    ∑ ω ∈ B, C.P ω * f ω = ∑ ω ∈ B, C.P ω * g ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * f ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * g ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨ω₁, hω₁, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : B.filter (fun ω => C.hist h ω = b) = C.atom h ω₁ := by
    ext ω
    simp only [Finset.mem_filter, mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hb1]
    · intro hω
      exact ⟨hsat ω₁ hω₁ ω hω, by rw [hω, hb1]⟩
  rw [hfiber]
  exact hfg ω₁ hω₁

/-- The per-step martingale identity summed over a time-`h`-saturated event. -/
theorem sum_saturated_step (h : ℕ) (B : Finset C.Ω)
    (hsat : ∀ ω ∈ B, ∀ ω', C.hist h ω' = C.hist h ω → ω' ∈ B) :
    ∑ ω ∈ B, C.P ω * C.condFuture (h + 1) ω
      = ∑ ω ∈ B, C.P ω * (C.condFuture h ω - C.sizeN h ω) := by
  refine C.sum_saturated h B hsat _ _ fun ω hm => ?_
  rw [← C.sum_atom_mul_condExp (C.condFuture (h + 1)) h ω]
  exact Finset.sum_congr rfl fun ω' _ => by rw [C.condFuture_succ_step]

/-- **Optional stopping over a window.** For a bounded stopping time `σ` that
has not yet fired at time `a`, averaging over a time-`a` atom: the expected
conditional future mass at `σ` is the mass at `a` minus the expected chunk
mass consumed in `[a, σ)`. -/
theorem sum_atom_optional_stopping (σ : C.Ω → ℕ) (hσ : C.IsStopping σ)
    (a : ℕ) (ω₀ : C.Ω) (ha : ∀ ω ∈ C.atom a ω₀, a ≤ σ ω)
    (N : ℕ) (haN : a ≤ N) (hN : ∀ ω ∈ C.atom a ω₀, σ ω ≤ N) :
    ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture (σ ω) ω
      = ∑ ω ∈ C.atom a ω₀,
          C.P ω * (C.condFuture a ω - ∑ j ∈ Finset.Ico a (σ ω), C.sizeN j ω) := by
  classical
  have key : ∀ n, a ≤ n →
      (∑ ω ∈ C.atom a ω₀, C.P ω *
        (C.condFuture (min (σ ω) n) ω
          + ∑ j ∈ Finset.Ico a (min (σ ω) n), C.sizeN j ω))
      = ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture a ω := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      refine Finset.sum_congr rfl fun ω hm => ?_
      have hmin : min (σ ω) a = a := by
        have := ha ω hm
        omega
      rw [hmin, Finset.Ico_self, Finset.sum_empty, add_zero]
    | succ n hn ih =>
      rw [← ih]
      have hdiff : ∑ ω ∈ C.atom a ω₀, (C.P ω *
            (C.condFuture (min (σ ω) (n + 1)) ω
              + ∑ j ∈ Finset.Ico a (min (σ ω) (n + 1)), C.sizeN j ω)
          - C.P ω *
            (C.condFuture (min (σ ω) n) ω
              + ∑ j ∈ Finset.Ico a (min (σ ω) n), C.sizeN j ω))
          = 0 := by
        have hsplit : ∀ ω ∈ C.atom a ω₀, C.P ω *
              (C.condFuture (min (σ ω) (n + 1)) ω
                + ∑ j ∈ Finset.Ico a (min (σ ω) (n + 1)), C.sizeN j ω)
            - C.P ω *
              (C.condFuture (min (σ ω) n) ω
                + ∑ j ∈ Finset.Ico a (min (σ ω) n), C.sizeN j ω)
            = if n < σ ω then
                C.P ω * (C.condFuture (n + 1) ω
                  - (C.condFuture n ω - C.sizeN n ω)) else 0 := by
          intro ω hm
          by_cases hσn : n < σ ω
          · rw [if_pos hσn]
            have hmin1 : min (σ ω) (n + 1) = n + 1 := by omega
            have hmin0 : min (σ ω) n = n := by omega
            rw [hmin1, hmin0, Finset.sum_Ico_succ_top hn]
            ring
          · rw [if_neg hσn]
            have hle : σ ω ≤ n := by omega
            have hmin1 : min (σ ω) (n + 1) = σ ω := by omega
            have hmin0 : min (σ ω) n = σ ω := by omega
            rw [hmin1, hmin0]
            ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_ite, Finset.sum_const_zero,
          add_zero]
        set B := (C.atom a ω₀).filter (fun ω => n < σ ω) with hB
        have hsat : ∀ ω ∈ B, ∀ ω', C.hist n ω' = C.hist n ω → ω' ∈ B := by
          intro ω hmB ω' hh
          rw [hB, Finset.mem_filter] at hmB ⊢
          refine ⟨?_, ?_⟩
          · rw [C.mem_atom] at hmB ⊢
            rw [C.href a n hn ω' ω hh]
            exact hmB.1
          · have hiff := hσ n ω ω' hh.symm
            have h2 := hmB.2
            by_contra hcon
            exact absurd (hiff.mpr (by omega)) (by omega)
        have hstep := C.sum_saturated_step n B hsat
        have : ∑ ω ∈ B, C.P ω * (C.condFuture (n + 1) ω
            - (C.condFuture n ω - C.sizeN n ω))
            = ∑ ω ∈ B, C.P ω * C.condFuture (n + 1) ω
              - ∑ ω ∈ B, C.P ω * (C.condFuture n ω - C.sizeN n ω) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
        rw [this, hstep, sub_self]
      have hsum := Finset.sum_sub_distrib (s := C.atom a ω₀)
        (f := fun ω => C.P ω *
          (C.condFuture (min (σ ω) (n + 1)) ω
            + ∑ j ∈ Finset.Ico a (min (σ ω) (n + 1)), C.sizeN j ω))
        (g := fun ω => C.P ω *
          (C.condFuture (min (σ ω) n) ω
            + ∑ j ∈ Finset.Ico a (min (σ ω) n), C.sizeN j ω))
      rw [hsum] at hdiff
      linarith
  have hfin := key N haN
  have hmin : ∀ ω ∈ C.atom a ω₀, min (σ ω) N = σ ω := by
    intro ω hm
    have := hN ω hm
    omega
  rw [Finset.sum_congr rfl (fun ω hm => by rw [hmin ω hm])] at hfin
  have hexp : ∑ ω ∈ C.atom a ω₀, C.P ω *
      (C.condFuture (σ ω) ω + ∑ j ∈ Finset.Ico a (σ ω), C.sizeN j ω)
      = ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture (σ ω) ω
        + ∑ ω ∈ C.atom a ω₀, C.P ω * ∑ j ∈ Finset.Ico a (σ ω), C.sizeN j ω := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hexp] at hfin
  have hgoal : ∑ ω ∈ C.atom a ω₀, C.P ω *
      (C.condFuture a ω - ∑ j ∈ Finset.Ico a (σ ω), C.sizeN j ω)
      = ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture a ω
        - ∑ ω ∈ C.atom a ω₀, C.P ω * ∑ j ∈ Finset.Ico a (σ ω), C.sizeN j ω := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hgoal]
  linarith

end ChunkSystemB

end KServer



/-! Draft for b6cb44c7 KServer.chunk_combining_zero_floor.
Helper layer 1: pointwise charging of a window's escape cost to its sub-chunks. -/

namespace KServer

namespace B6cb

variable {X : Type*} [MetricSpace X]

/-- The escape cost of a window made of consecutive sub-chunks `L`, served after history `h`
at price `p'`, charged sub-chunk by sub-chunk at the smaller price `pe`: each sub-chunk up to and
including the one where the rule fires pays its own `pe`-escape cost, and the firing one pays the
price difference `p' - pe` on top. -/
noncomputable def chargeSum (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (pe p' : ℝ) :
    List (Set X) → List (List (Set X)) → ℝ
  | _, [] => 0
  | h, χ :: L =>
    match bailTime bail h χ with
    | some _ => E.bailCost bail h χ pe + (p' - pe)
    | none => E.bailCost bail h χ pe + chargeSum E bail pe p' (h ++ χ) L

theorem bailTime_nil (bail : List (Set X) → Bool) (h : List (Set X)) :
    bailTime bail h [] = none := by
  unfold bailTime
  simp

theorem bailCost_nil (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h : List (Set X)) (p : ℝ) : E.bailCost bail h [] p = 0 := by
  rw [E.bailCost_of_no_bail bail h [] p (bailTime_nil bail h)]
  unfold EvaderAlgorithm.costOn
  simp

/-- **Window charging identity.** -/
theorem bailCost_flatten_eq_chargeSum (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (pe p' : ℝ) : ∀ (L : List (List (Set X))) (h : List (Set X)),
    E.bailCost bail h L.flatten p' = chargeSum E bail pe p' h L
  | [], h => by
    simp only [List.flatten_nil, chargeSum]
    exact bailCost_nil E bail h p'
  | χ :: L, h => by
    rw [List.flatten_cons]
    rcases hq : bailTime bail h χ with - | q
    · rw [E.bailCost_append_of_no_bail bail h χ L.flatten p' hq,
        bailCost_flatten_eq_chargeSum E bail pe p' L (h ++ χ)]
      simp only [chargeSum, hq]
      rw [E.bailCost_of_no_bail bail h χ pe hq]
    · rw [E.bailCost_append_of_bail bail h χ L.flatten p' hq,
        E.bailCost_price_of_bail bail h χ pe p' hq]
      simp only [chargeSum, hq]


/-- Sub-chunk `l` of a chunk list (empty past the end). -/
def sub (cs : List (List (Set X))) (l : ℕ) : List (Set X) := cs.getD l []

/-- History before sub-chunk `l`. -/
def pre (cs : List (List (Set X))) (l : ℕ) : List (Set X) := (cs.take l).flatten

omit [MetricSpace X] in
theorem pre_succ (cs : List (List (Set X))) {l : ℕ} (hl : l < cs.length) :
    pre cs (l + 1) = pre cs l ++ sub cs l := by
  unfold pre sub
  rw [List.take_add_one, List.flatten_append, List.getElem?_eq_getElem hl]
  simp [List.getElem?_eq_getElem hl]

omit [MetricSpace X] in
theorem window_cons (cs : List (List (Set X))) {a b : ℕ} (hab : a < b) (hb : b ≤ cs.length) :
    (cs.drop a).take (b - a) = sub cs a :: (cs.drop (a + 1)).take (b - (a + 1)) := by
  have ha : a < cs.length := lt_of_lt_of_le hab hb
  rw [List.drop_eq_getElem_cons ha]
  have : b - a = (b - (a + 1)) + 1 := by omega
  rw [this, List.take_succ_cons]
  unfold sub
  rw [List.getD_eq_getElem _ _ ha]

open Classical in
/-- **Window charging, indicator form.** The `p'`-escape cost of the window `[a, b)` of a chunk
list equals the sum of the `pe`-escape costs of its sub-chunks that start before the rule has
fired, plus `p' - pe` if the rule fires somewhere in the window. -/
theorem chargeSum_window (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (pe p' : ℝ)
    (cs : List (List (Set X))) (b : ℕ) (hb : b ≤ cs.length) :
    ∀ k a, b - a = k → a ≤ b →
    chargeSum E bail pe p' (pre cs a) ((cs.drop a).take (b - a))
      = (∑ l ∈ Finset.Ico a b,
          if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
          then E.bailCost bail (pre cs l) (sub cs l) pe else 0)
        + (if (∃ l ∈ Finset.Ico a b, bailTime bail (pre cs l) (sub cs l) ≠ none)
           then p' - pe else 0) := by
  intro k
  induction k with
  | zero =>
    intro a hk hab
    have hba : b = a := by omega
    subst hba
    simp [chargeSum]
  | succ k ih =>
    intro a hk hab
    have hlt : a < b := by omega
    have ha : a < cs.length := lt_of_lt_of_le hlt hb
    rw [window_cons cs hlt hb]
    have hIco : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
      rw [Finset.insert_Ico_add_one_left_eq_Ico hlt]
    rw [hIco, Finset.sum_insert (by simp)]
    have hself : (∀ l' ∈ Finset.Ico a a, bailTime bail (pre cs l') (sub cs l') = none) := by
      simp
    rw [if_pos hself]
    rcases hq : bailTime bail (pre cs a) (sub cs a) with - | q
    · -- no fire in sub-chunk `a`: recurse
      simp only [chargeSum, hq]
      rw [← pre_succ cs ha, ih (a + 1) (by omega) (by omega)]
      have hcongr : ∀ l ∈ Finset.Ico (a + 1) b,
          (if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
            then E.bailCost bail (pre cs l) (sub cs l) pe else 0)
          = (if (∀ l' ∈ Finset.Ico (a + 1) l, bailTime bail (pre cs l') (sub cs l') = none)
            then E.bailCost bail (pre cs l) (sub cs l) pe else 0) := by
        intro l hl
        have hl' : a + 1 ≤ l := (Finset.mem_Ico.mp hl).1
        congr 1
        apply propext
        constructor
        · intro H l' hl''
          exact H l' (by simp only [Finset.mem_Ico] at hl'' ⊢; omega)
        · intro H l' hl''
          by_cases hla : l' = a
          · subst hla; exact hq
          · exact H l' (by simp only [Finset.mem_Ico] at hl'' ⊢; omega)
      rw [Finset.sum_congr rfl hcongr]
      have hfire : (∃ l ∈ insert a (Finset.Ico (a + 1) b),
            bailTime bail (pre cs l) (sub cs l) ≠ none)
          ↔ (∃ l ∈ Finset.Ico (a + 1) b, bailTime bail (pre cs l) (sub cs l) ≠ none) := by
        constructor
        · rintro ⟨l, hl, hne⟩
          rcases Finset.mem_insert.mp hl with rfl | hl
          · exact absurd hq hne
          · exact ⟨l, hl, hne⟩
        · rintro ⟨l, hl, hne⟩
          exact ⟨l, Finset.mem_insert_of_mem hl, hne⟩
      rw [if_congr hfire rfl rfl]
      ring
    · -- fires in sub-chunk `a`
      simp only [chargeSum, hq]
      have hzero : ∀ l ∈ Finset.Ico (a + 1) b,
          (if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
            then E.bailCost bail (pre cs l) (sub cs l) pe else 0) = 0 := by
        intro l hl
        have hl' : a + 1 ≤ l := (Finset.mem_Ico.mp hl).1
        rw [if_neg]
        intro H
        have := H a (by simp only [Finset.mem_Ico]; omega)
        rw [hq] at this
        exact Option.some_ne_none q this
      rw [Finset.sum_eq_zero hzero]
      have hfire : (∃ l ∈ insert a (Finset.Ico (a + 1) b),
            bailTime bail (pre cs l) (sub cs l) ≠ none) :=
        ⟨a, Finset.mem_insert_self _ _, by rw [hq]; exact Option.some_ne_none q⟩
      rw [if_pos hfire]
      ring

omit [MetricSpace X] in
/-- `pre` and `sub` below `l` depend only on the first `l` sub-chunks. -/
theorem pre_sub_of_take_eq {cs cs' : List (List (Set X))} {l : ℕ}
    (h : cs.take l = cs'.take l) {l' : ℕ} (hl : l' < l) :
    pre cs l' = pre cs' l' ∧ sub cs l' = sub cs' l' := by
  constructor
  · unfold pre
    have h1 : cs.take l' = (cs.take l).take l' := by
      rw [List.take_take, Nat.min_eq_left (le_of_lt hl)]
    have h2 : cs'.take l' = (cs'.take l).take l' := by
      rw [List.take_take, Nat.min_eq_left (le_of_lt hl)]
    rw [h1, h2, h]
  · unfold sub
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      ← List.getElem?_take_of_lt (l := cs) hl, ← List.getElem?_take_of_lt (l := cs') hl, h]

section Sys

variable {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- The chunk list of an outcome. -/
def cl (ω : C.Ω) : List (List (Set X)) := List.ofFn (C.chunk ω)

theorem cl_length (ω : C.Ω) : (cl C ω).length = C.m := by
  simp [cl]

theorem sub_cl (ω : C.Ω) (i : Fin C.m) : sub (cl C ω) i = C.chunk ω i := by
  unfold sub cl
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- Size of sub-chunk `l` (zero past the end). -/
noncomputable def szN (ω : C.Ω) (l : ℕ) : ℝ := if h : l < C.m then C.size ω ⟨l, h⟩ else 0

/-- Equal time-`l` histories give equal first `l` sub-chunks. -/
theorem take_cl_eq {l : ℕ} {ω ω' : C.Ω} (hh : C.hist l ω = C.hist l ω') :
    (cl C ω).take l = (cl C ω').take l := by
  apply List.ext_getElem
  · simp [cl]
  · intro j h1 h2
    simp only [List.getElem_take, cl, List.getElem_ofFn]
    have hj : j < l := by
      simp [cl] at h1
      omega
    have hjm : j < C.m := by
      simp [cl] at h1
      omega
    exact C.hadapt ⟨j, hjm⟩ ω ω' (C.href (j + 1) l (by omega) ω ω' hh)

/-- Summation over a time-`h`-saturated set: an atomwise inequality lifts. -/
theorem sum_saturated_le (h : ℕ) (B : Finset C.Ω)
    (hsat : ∀ ω ∈ B, ∀ ω', C.hist h ω' = C.hist h ω → ω' ∈ B)
    (f g : C.Ω → ℝ)
    (hfg : ∀ ω ∈ B, ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * g ω') :
    ∑ ω ∈ B, C.P ω * f ω ≤ ∑ ω ∈ B, C.P ω * g ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * f ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * g ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨ω₁, hω₁, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : B.filter (fun ω => C.hist h ω = b) = C.atom h ω₁ := by
    ext ω
    simp only [Finset.mem_filter, ChunkSystemB.mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hb1]
    · intro hω
      exact ⟨hsat ω₁ hω₁ ω hω, by rw [hω, hb1]⟩
  rw [hfiber]
  exact hfg ω₁ hω₁

/-- The input cost bound, summed over a time-`i`-saturated set. -/
theorem hcost_saturated (i : Fin C.m) (B : Finset C.Ω)
    (hsat : ∀ ω ∈ B, ∀ ω', C.hist i ω' = C.hist i ω → ω' ∈ B)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) :
    ∑ ω ∈ B, C.P ω * C.size ω i
      ≤ ∑ ω ∈ B, C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten)
          (C.chunk ω i) price := by
  refine sum_saturated_le C i B hsat _ _ fun ω₀ _ => ?_
  have hc := C.hcost i ω₀ E bail
  have hatom : Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀) = C.atom i ω₀ := rfl
  rw [hatom] at hc
  have hconst : ∑ ω' ∈ C.atom i ω₀, C.P ω' * C.size ω' i
      = C.size ω₀ i * ∑ ω' ∈ C.atom i ω₀, C.P ω' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' hm => ?_
    rw [C.hsmeas i ω' ω₀ (C.mem_atom.mp hm)]
    ring
  rw [hconst]
  exact hc

/-- Re-index a window sum as a sum over all indices below `m`. -/
theorem window_sum_range (σ : C.Ω → ℕ) (hσm : ∀ ω, σ ω ≤ C.m) (a : ℕ)
    (nf : C.Ω → ℕ → Prop) [∀ ω l, Decidable (nf ω l)] (x : C.Ω → ℕ → ℝ) (ω : C.Ω) :
    (∑ l ∈ Finset.Ico a (σ ω), if nf ω l then x ω l else 0)
      = ∑ l ∈ Finset.range C.m, if (l ∈ Finset.Ico a (σ ω) ∧ nf ω l) then x ω l else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  have := hσm ω
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h1, h2⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩

open Classical in
/-- **Window charging in expectation.** Over a time-`a` atom, the `p'`-escape cost of the window
`[a, σ)` (σ a stopping time) is at least the expected size of its sub-chunks that start before the
escape rule fires, plus `p' - price` times the firing probability. -/
theorem window_charge_ge (a : ℕ) (ω₀ : C.Ω) (σ : C.Ω → ℕ)
    (hσ : ∀ (h : ℕ) (ω ω' : C.Ω), C.hist h ω = C.hist h ω' → (σ ω ≤ h ↔ σ ω' ≤ h))
    (hσm : ∀ ω, σ ω ≤ C.m) (ha : ∀ ω ∈ C.atom a ω₀, a ≤ σ ω)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ) :
    ∑ ω ∈ C.atom a ω₀, C.P ω *
        ((∑ l ∈ Finset.Ico a (σ ω),
          if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre (cl C ω) l') (sub (cl C ω) l') = none)
          then szN C ω l else 0)
        + (if (∃ l ∈ Finset.Ico a (σ ω), bailTime bail (pre (cl C ω) l) (sub (cl C ω) l) ≠ none)
           then p' - price else 0))
      ≤ ∑ ω ∈ C.atom a ω₀, C.P ω *
          E.bailCost bail (pre (cl C ω) a) (((cl C ω).drop a).take (σ ω - a)).flatten p' := by
  set A := C.atom a ω₀ with hA
  set nf : C.Ω → ℕ → Prop := fun ω l =>
    ∀ l' ∈ Finset.Ico a l, bailTime bail (pre (cl C ω) l') (sub (cl C ω) l') = none with hnf
  set fr : C.Ω → Prop := fun ω =>
    ∃ l ∈ Finset.Ico a (σ ω), bailTime bail (pre (cl C ω) l) (sub (cl C ω) l) ≠ none with hfr
  have hR : ∀ ω ∈ A, E.bailCost bail (pre (cl C ω) a) (((cl C ω).drop a).take (σ ω - a)).flatten p'
      = (∑ l ∈ Finset.Ico a (σ ω), if nf ω l
          then E.bailCost bail (pre (cl C ω) l) (sub (cl C ω) l) price else 0)
        + (if fr ω then p' - price else 0) := by
    intro ω hω
    rw [bailCost_flatten_eq_chargeSum E bail price p']
    exact chargeSum_window E bail price p' (cl C ω) (σ ω)
      (by rw [cl_length]; exact hσm ω) (σ ω - a) a rfl (ha ω hω)
  refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun ω hω => by rw [hR ω hω]).symm
  simp only [mul_add, Finset.sum_add_distrib]
  refine add_le_add ?_ le_rfl
  -- swap the sums
  have hswap : ∀ (x : C.Ω → ℕ → ℝ),
      ∑ ω ∈ A, C.P ω * (∑ l ∈ Finset.Ico a (σ ω), if nf ω l then x ω l else 0)
        = ∑ l ∈ Finset.range C.m, ∑ ω ∈ A,
            (if (l ∈ Finset.Ico a (σ ω) ∧ nf ω l) then C.P ω * x ω l else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [window_sum_range C σ hσm a nf x ω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [hswap, hswap]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlm : l < C.m := Finset.mem_range.mp hl
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  set B := A.filter (fun ω => l ∈ Finset.Ico a (σ ω) ∧ nf ω l) with hB
  have hsz : ∀ ω ∈ B, C.P ω * szN C ω l = C.P ω * C.size ω ⟨l, hlm⟩ := by
    intro ω _
    simp [szN, hlm]
  have hbc : ∀ ω ∈ B, C.P ω * E.bailCost bail (pre (cl C ω) l) (sub (cl C ω) l) price
      = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take (⟨l, hlm⟩ : Fin C.m)).flatten)
          (C.chunk ω ⟨l, hlm⟩) price := by
    intro ω _
    rw [show sub (cl C ω) l = C.chunk ω ⟨l, hlm⟩ from sub_cl C ω ⟨l, hlm⟩]
    rfl
  rw [Finset.sum_congr rfl hsz, Finset.sum_congr rfl hbc]
  refine hcost_saturated C ⟨l, hlm⟩ B ?_ E bail
  -- saturation of `B` at time `l`
  intro ω hω ω' hh
  rw [hB, Finset.mem_filter] at hω ⊢
  obtain ⟨hωA, hlI, hnfω⟩ := hω
  have hal : a ≤ l := (Finset.mem_Ico.mp hlI).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, ChunkSystemB.mem_atom] at hωA ⊢
    rw [C.href a l hal ω' ω hh]
    exact hωA
  · have hiff := hσ l ω ω' hh.symm
    simp only [Finset.mem_Ico] at hlI ⊢
    refine ⟨hal, ?_⟩
    by_contra hc
    exact absurd (hiff.mpr (by omega)) (by omega)
  · have htake := take_cl_eq C (l := l) hh
    intro l' hl'
    have hl'l : l' < l := (Finset.mem_Ico.mp hl').2
    obtain ⟨hp, hs⟩ := pre_sub_of_take_eq htake hl'l
    rw [hp, hs]
    exact hnfω l' hl'

open Classical in
/-- Pointwise bookkeeping for one outcome: the sizes of a window split into those started before
the escape rule fires and the remainder after the (unique) first firing sub-chunk. -/
theorem window_split (cs : List (List (Set X))) (bail : List (Set X) → Bool)
    (a b : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    (∑ l ∈ Finset.Ico a b, x l)
      = (∑ l ∈ Finset.Ico a b,
          if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
          then x l else 0)
        + ∑ r ∈ Finset.Ico a b,
          (if (bailTime bail (pre cs r) (sub cs r) ≠ none ∧
              ∀ l' ∈ Finset.Ico a r, bailTime bail (pre cs l') (sub cs l') = none)
            then ∑ l ∈ Finset.Ico (r + 1) b, x l else 0)
    ∧ (if (∃ l ∈ Finset.Ico a b, bailTime bail (pre cs l) (sub cs l) ≠ none) then c else 0)
      = ∑ r ∈ Finset.Ico a b,
          (if (bailTime bail (pre cs r) (sub cs r) ≠ none ∧
              ∀ l' ∈ Finset.Ico a r, bailTime bail (pre cs l') (sub cs l') = none)
            then c else 0) := by
  set F : ℕ → Prop := fun l => bailTime bail (pre cs l) (sub cs l) ≠ none with hF
  by_cases hex : ∃ l ∈ Finset.Ico a b, F l
  · have hex' : ∃ r, r ∈ Finset.Ico a b ∧ F r := hex
    set r0 := Nat.find hex' with hr0
    have hr0mem : r0 ∈ Finset.Ico a b ∧ F r0 := Nat.find_spec hex'
    have hr0min : ∀ r < r0, ¬ (r ∈ Finset.Ico a b ∧ F r) := fun r hr => Nat.find_min hex' hr
    have hab0 := Finset.mem_Ico.mp hr0mem.1
    have hnoF : ∀ l', a ≤ l' → l' < r0 → bailTime bail (pre cs l') (sub cs l') = none := by
      intro l' h1 h2
      by_contra hc
      exact hr0min l' h2 ⟨Finset.mem_Ico.mpr ⟨h1, by omega⟩, hc⟩
    have hff : ∀ r ∈ Finset.Ico a b, (F r ∧
        ∀ l' ∈ Finset.Ico a r, bailTime bail (pre cs l') (sub cs l') = none) ↔ r = r0 := by
      intro r hr
      have hr' := Finset.mem_Ico.mp hr
      constructor
      · rintro ⟨hFr, hno⟩
        have hle : r0 ≤ r := Nat.find_min' hex' ⟨hr, hFr⟩
        by_contra hne
        have hlt : r0 < r := lt_of_le_of_ne hle (Ne.symm hne)
        exact hr0mem.2 (hno r0 (Finset.mem_Ico.mpr ⟨hab0.1, hlt⟩))
      · rintro rfl
        exact ⟨hr0mem.2, fun l' hl' => hnoF l' (Finset.mem_Ico.mp hl').1 (Finset.mem_Ico.mp hl').2⟩
    have hnf : ∀ l ∈ Finset.Ico a b,
        (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none) ↔ l ≤ r0 := by
      intro l hl
      constructor
      · intro H
        by_contra hc
        exact hr0mem.2 (H r0 (Finset.mem_Ico.mpr ⟨hab0.1, by omega⟩))
      · intro hle l' hl'
        exact hnoF l' (Finset.mem_Ico.mp hl').1 (by have := (Finset.mem_Ico.mp hl').2; omega)
    have hsingle : ∀ (g : ℕ → ℝ), (∑ r ∈ Finset.Ico a b,
        (if (F r ∧ ∀ l' ∈ Finset.Ico a r, bailTime bail (pre cs l') (sub cs l') = none)
          then g r else 0)) = g r0 := by
      intro g
      rw [Finset.sum_eq_single r0]
      · rw [if_pos ((hff r0 hr0mem.1).mpr rfl)]
      · intro r hr hne
        rw [if_neg (fun h => hne ((hff r hr).mp h))]
      · intro h
        exact absurd hr0mem.1 h
    refine ⟨?_, ?_⟩
    · rw [hsingle (fun r => ∑ l ∈ Finset.Ico (r + 1) b, x l)]
      have h1 : a ≤ r0 + 1 := by omega
      have h2 : r0 + 1 ≤ b := by omega
      rw [← Finset.sum_Ico_consecutive _ h1 h2, ← Finset.sum_Ico_consecutive _ h1 h2]
      have hA : ∑ l ∈ Finset.Ico a (r0 + 1),
          (if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
            then x l else 0) = ∑ l ∈ Finset.Ico a (r0 + 1), x l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl' := Finset.mem_Ico.mp hl
        rw [if_pos ((hnf l (Finset.mem_Ico.mpr ⟨hl'.1, by omega⟩)).mpr (by omega))]
      have hB : ∑ l ∈ Finset.Ico (r0 + 1) b,
          (if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
            then x l else 0) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hl' := Finset.mem_Ico.mp hl
        rw [if_neg (fun h => by
          have := (hnf l (Finset.mem_Ico.mpr ⟨by omega, hl'.2⟩)).mp h
          omega)]
      rw [hA, hB]
      ring
    · rw [if_pos hex, hsingle (fun _ => c)]
  · have hnone : ∀ l ∈ Finset.Ico a b, bailTime bail (pre cs l) (sub cs l) = none := by
      intro l hl
      by_contra hc
      exact hex ⟨l, hl, hc⟩
    refine ⟨?_, ?_⟩
    · have hA : ∑ l ∈ Finset.Ico a b,
          (if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre cs l') (sub cs l') = none)
            then x l else 0) = ∑ l ∈ Finset.Ico a b, x l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [if_pos (fun l' hl' => hnone l' (Finset.mem_Ico.mpr
          ⟨(Finset.mem_Ico.mp hl').1, lt_trans (Finset.mem_Ico.mp hl').2 (Finset.mem_Ico.mp hl).2⟩))]
      have hB : ∑ r ∈ Finset.Ico a b,
          (if (F r ∧ ∀ l' ∈ Finset.Ico a r, bailTime bail (pre cs l') (sub cs l') = none)
            then ∑ l ∈ Finset.Ico (r + 1) b, x l else 0) = 0 := by
        refine Finset.sum_eq_zero fun r hr => ?_
        rw [if_neg (fun h => h.1 (hnone r hr))]
      rw [hA, hB, add_zero]
    · rw [if_neg hex]
      symm
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [if_neg (fun h => h.1 (hnone r hr))]

open Classical in
/-- **A window pays its expected mass.** If, at every time `h` inside the window `[a, σ)`, the
expected remaining window mass is at most `K ≤ p' - price`, then over a time-`a` atom the expected
`p'`-escape cost of the window is at least its expected mass. -/
theorem window_cost_ge_mass (a : ℕ) (ω₀ : C.Ω) (σ : C.Ω → ℕ)
    (hσ : ∀ (h : ℕ) (ω ω' : C.Ω), C.hist h ω = C.hist h ω' → (σ ω ≤ h ↔ σ ω' ≤ h))
    (hσm : ∀ ω, σ ω ≤ C.m) (ha : ∀ ω ∈ C.atom a ω₀, a ≤ σ ω)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' K : ℝ) (hK : K ≤ p' - price)
    (hR : ∀ h, a ≤ h → ∀ ω ∈ C.atom a ω₀, h ≤ σ ω →
      ∑ ω' ∈ C.atom h ω, C.P ω' * ∑ l ∈ Finset.Ico h (σ ω'), szN C ω' l
        ≤ K * ∑ ω' ∈ C.atom h ω, C.P ω') :
    ∑ ω ∈ C.atom a ω₀, C.P ω * ∑ l ∈ Finset.Ico a (σ ω), szN C ω l
      ≤ ∑ ω ∈ C.atom a ω₀, C.P ω *
          E.bailCost bail (pre (cl C ω) a) (((cl C ω).drop a).take (σ ω - a)).flatten p' := by
  refine le_trans ?_ (window_charge_ge C a ω₀ σ hσ hσm ha E bail p')
  set A := C.atom a ω₀ with hA
  set ff : C.Ω → ℕ → Prop := fun ω r =>
    bailTime bail (pre (cl C ω) r) (sub (cl C ω) r) ≠ none ∧
      ∀ l' ∈ Finset.Ico a r, bailTime bail (pre (cl C ω) l') (sub (cl C ω) l') = none with hff
  set Rem : C.Ω → ℕ → ℝ := fun ω r => ∑ l ∈ Finset.Ico (r + 1) (σ ω), szN C ω l with hRem
  -- pointwise split
  have hpt : ∀ ω ∈ A, C.P ω *
        ((∑ l ∈ Finset.Ico a (σ ω),
          if (∀ l' ∈ Finset.Ico a l, bailTime bail (pre (cl C ω) l') (sub (cl C ω) l') = none)
          then szN C ω l else 0)
        + (if (∃ l ∈ Finset.Ico a (σ ω), bailTime bail (pre (cl C ω) l) (sub (cl C ω) l) ≠ none)
           then p' - price else 0))
      = C.P ω * ∑ l ∈ Finset.Ico a (σ ω), szN C ω l
        + (C.P ω * (∑ r ∈ Finset.Ico a (σ ω), if ff ω r then (p' - price) else 0)
          - C.P ω * (∑ r ∈ Finset.Ico a (σ ω), if ff ω r then Rem ω r else 0)) := by
    intro ω _
    obtain ⟨h1, h2⟩ := window_split (cl C ω) bail a (σ ω) (fun l => szN C ω l) (p' - price)
    rw [h2, h1]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  refine le_add_of_nonneg_right ?_
  rw [Finset.sum_sub_distrib, sub_nonneg]
  -- compare the two firing sums index by index
  have hswap : ∀ (x : C.Ω → ℕ → ℝ),
      ∑ ω ∈ A, C.P ω * (∑ l ∈ Finset.Ico a (σ ω), if ff ω l then x ω l else 0)
        = ∑ l ∈ Finset.range C.m, ∑ ω ∈ A,
            (if (l ∈ Finset.Ico a (σ ω) ∧ ff ω l) then C.P ω * x ω l else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [window_sum_range C σ hσm a ff x ω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [hswap (fun ω r => Rem ω r), hswap (fun _ _ => p' - price)]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  set B := A.filter (fun ω => r ∈ Finset.Ico a (σ ω) ∧ ff ω r) with hB
  have hsat : ∀ ω ∈ B, ∀ ω', C.hist (r + 1) ω' = C.hist (r + 1) ω → ω' ∈ B := by
    intro ω hω ω' hh
    rw [hB, Finset.mem_filter] at hω ⊢
    obtain ⟨hωA, hrI, hffω⟩ := hω
    have har : a ≤ r := (Finset.mem_Ico.mp hrI).1
    refine ⟨?_, ?_, ?_⟩
    · rw [hA, ChunkSystemB.mem_atom] at hωA ⊢
      rw [C.href a (r + 1) (by omega) ω' ω hh]
      exact hωA
    · have hh' : C.hist r ω = C.hist r ω' := (C.href r (r + 1) (by omega) ω' ω hh).symm
      have hiff := hσ r ω ω' hh'
      simp only [Finset.mem_Ico] at hrI ⊢
      refine ⟨har, ?_⟩
      by_contra hc
      exact absurd (hiff.mpr (by omega)) (by omega)
    · have htake := take_cl_eq C (l := r + 1) hh
      obtain ⟨hp, hs⟩ := pre_sub_of_take_eq htake (show r < r + 1 by omega)
      refine ⟨by rw [hp, hs]; exact hffω.1, ?_⟩
      intro l' hl'
      obtain ⟨hp', hs'⟩ := pre_sub_of_take_eq htake
        (show l' < r + 1 by have := (Finset.mem_Ico.mp hl').2; omega)
      rw [hp', hs']
      exact hffω.2 l' hl'
  refine sum_saturated_le C (r + 1) B hsat _ _ fun ω hω => ?_
  rw [hB, Finset.mem_filter] at hω
  obtain ⟨hωA, hrI, _⟩ := hω
  have hrI' := Finset.mem_Ico.mp hrI
  have h1 := hR (r + 1) (by omega) ω hωA (by omega)
  have hmass : 0 ≤ ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' :=
    Finset.sum_nonneg fun ω' _ => le_of_lt (C.hP ω')
  calc ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' * Rem ω' r
      = ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' * ∑ l ∈ Finset.Ico (r + 1) (σ ω'), szN C ω' l := rfl
    _ ≤ K * ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' := h1
    _ ≤ (p' - price) * ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' := mul_le_mul_of_nonneg_right hK hmass
    _ = ∑ ω' ∈ C.atom (r + 1) ω, C.P ω' * (p' - price) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem szN_eq_sizeN (ω : C.Ω) (l : ℕ) : szN C ω l = C.sizeN l ω := rfl

/-- **Remaining window mass from the conditional future mass.** If inside the window `[a, σ)`
the conditional future mass stays at most `U`, and at the window end it is at least `Lnext - d`,
then at every time inside the window the expected remaining window mass is at most
`U - (Lnext - d)` (optional stopping). This is the hypothesis `hR` of `window_cost_ge_mass`. -/
theorem remaining_le (a : ℕ) (ω₀ : C.Ω) (σ : C.Ω → ℕ)
    (hσ : ∀ (h : ℕ) (ω ω' : C.Ω), C.hist h ω = C.hist h ω' → (σ ω ≤ h ↔ σ ω' ≤ h))
    (hσm : ∀ ω, σ ω ≤ C.m) (U Lnext d : ℝ)
    (hU : ∀ ω ∈ C.atom a ω₀, ∀ h, a ≤ h → h ≤ σ ω → C.condFuture h ω ≤ U)
    (hL : ∀ ω ∈ C.atom a ω₀, Lnext - d ≤ C.condFuture (σ ω) ω) :
    ∀ h, a ≤ h → ∀ ω ∈ C.atom a ω₀, h ≤ σ ω →
      ∑ ω' ∈ C.atom h ω, C.P ω' * ∑ l ∈ Finset.Ico h (σ ω'), szN C ω' l
        ≤ (U - (Lnext - d)) * ∑ ω' ∈ C.atom h ω, C.P ω' := by
  intro h hah ω hω hhσ
  have hin : ∀ ω' ∈ C.atom h ω, ω' ∈ C.atom a ω₀ := by
    intro ω' hω'
    rw [ChunkSystemB.mem_atom] at hω' hω ⊢
    rw [C.href a h hah ω' ω hω']
    exact hω
  have hge : ∀ ω' ∈ C.atom h ω, h ≤ σ ω' := by
    intro ω' hω'
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · omega
    · have hh' : C.hist (h - 1) ω = C.hist (h - 1) ω' :=
        (C.href (h - 1) h (by omega) ω' ω (ChunkSystemB.mem_atom C |>.mp hω')).symm
      have hiff := hσ (h - 1) ω ω' hh'
      by_contra hc
      have : σ ω ≤ h - 1 := hiff.mpr (by omega)
      omega
  have hos := C.sum_atom_optional_stopping σ hσ h ω hge C.m
    (le_trans hhσ (hσm ω)) (fun ω' _ => hσm ω')
  have hsum : ∑ ω' ∈ C.atom h ω, C.P ω' * ∑ l ∈ Finset.Ico h (σ ω'), szN C ω' l
      = ∑ ω' ∈ C.atom h ω, C.P ω' * C.condFuture h ω'
        - ∑ ω' ∈ C.atom h ω, C.P ω' * C.condFuture (σ ω') ω' := by
    rw [hos, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    simp only [szN_eq_sizeN]
    ring
  rw [hsum]
  have h1 : ∑ ω' ∈ C.atom h ω, C.P ω' * C.condFuture h ω'
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * U :=
    Finset.sum_le_sum fun ω' hω' => mul_le_mul_of_nonneg_left
      (hU ω' (hin ω' hω') h hah (hge ω' hω')) (le_of_lt (C.hP ω'))
  have h2 : ∑ ω' ∈ C.atom h ω, C.P ω' * (Lnext - d)
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * C.condFuture (σ ω') ω' :=
    Finset.sum_le_sum fun ω' hω' => mul_le_mul_of_nonneg_left
      (hL ω' (hin ω' hω')) (le_of_lt (C.hP ω'))
  have h3 : ∑ ω' ∈ C.atom h ω, C.P ω' * U - ∑ ω' ∈ C.atom h ω, C.P ω' * (Lnext - d)
      = (U - (Lnext - d)) * ∑ ω' ∈ C.atom h ω, C.P ω' := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  linarith

end Sys

end B6cb


end KServer

/-! Step A: one-step surgery removing an upward move of the conditional future mass. -/

namespace KServer

namespace B6cb

theorem sum_subtype_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (q : α → Prop) [DecidablePred q] (f : α → ℝ) :
    ∑ v ∈ (Finset.univ : Finset {x // p x}).filter (fun v => q v.1), f v.1
      = ∑ w ∈ Finset.univ.filter (fun w => p w ∧ q w), f w := by
  rw [Finset.sum_filter]
  rw [← Finset.sum_subtype (Finset.univ.filter p) (fun x => by simp) (fun w => if q w then f w else 0)]
  rw [← Finset.sum_filter, Finset.filter_filter]

section Surgery

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t 0 cB T pe mL) (h : ℕ) (w0 : C.Ω)

/-- The surgery scale on the chosen child. -/
noncomputable def lam : ℝ := C.condFuture h w0 / C.condFuture (h + 1) w0

/-- The reweighting factor of the chosen child. -/
noncomputable def cc : ℝ := C.mass (C.atom h w0) / C.mass (C.atom (h + 1) w0)

noncomputable def P2 (w : C.Ω) : ℝ :=
  if C.hist h w = C.hist h w0 then C.P w * cc C h w0 else C.P w

noncomputable def size2 (w : C.Ω) (j : Fin C.m) : ℝ :=
  if C.hist h w = C.hist h w0 ∧ h ≤ j.val then
    (if j.val = h then 0 else lam C h w0 * C.size w j) else C.size w j

/-- The future mass after surgery (as a function on the old sample space). -/
noncomputable def fut2 (k : ℕ) (w : C.Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => k ≤ i.val), size2 C h w0 w i

variable {C h w0}

theorem size_nonneg' (w : C.Ω) (i : Fin C.m) : 0 ≤ C.size w i := (C.hsize w i).1

theorem cc_pos : 0 < cc C h w0 :=
  div_pos (C.mass_atom_pos h w0) (C.mass_atom_pos (h + 1) w0)

theorem cc_mul : cc C h w0 * C.mass (C.atom (h + 1) w0) = C.mass (C.atom h w0) := by
  unfold cc
  exact div_mul_cancel₀ _ (ne_of_gt (C.mass_atom_pos (h + 1) w0))

variable (hv : C.condFuture h w0 < C.condFuture (h + 1) w0)
include hv

theorem F1_pos : 0 < C.condFuture (h + 1) w0 :=
  lt_of_le_of_lt (C.condFuture_nonneg (le_refl 0) h w0) hv

theorem lam_nonneg : 0 ≤ lam C h w0 :=
  div_nonneg (C.condFuture_nonneg (le_refl 0) h w0) (le_of_lt (F1_pos hv))

theorem lam_le_one : lam C h w0 ≤ 1 := by
  unfold lam
  rw [div_le_one (F1_pos hv)]
  exact le_of_lt hv

theorem lam_mul : lam C h w0 * C.condFuture (h + 1) w0 = C.condFuture h w0 := by
  unfold lam
  exact div_mul_cancel₀ _ (ne_of_gt (F1_pos hv))

omit hv

theorem keep_inA {w : C.Ω}
    (hk : C.hist h w ≠ C.hist h w0 ∨ C.hist (h + 1) w = C.hist (h + 1) w0)
    (hA : C.hist h w = C.hist h w0) : C.hist (h + 1) w = C.hist (h + 1) w0 := by
  rcases hk with hk | hk
  · exact absurd hA hk
  · exact hk

theorem inA_of_inA' {w : C.Ω} (hA' : C.hist (h + 1) w = C.hist (h + 1) w0) :
    C.hist h w = C.hist h w0 :=
  C.href h (h + 1) (Nat.le_succ h) w w0 hA'

/-- Decomposition of a kept-set sum. -/
theorem keep_sum_split (q : C.Ω → Prop) [DecidablePred q] (g : C.Ω → ℝ) :
    ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ q w), P2 C h w0 w * g w
      = ∑ w ∈ Finset.univ.filter (fun w => q w ∧ C.hist h w ≠ C.hist h w0), C.P w * g w
        + cc C h w0 * ∑ w ∈ Finset.univ.filter
            (fun w => q w ∧ C.hist (h + 1) w = C.hist (h + 1) w0), C.P w * g w := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun w => C.hist h w = C.hist h w0)]
  rw [add_comm]
  congr 1
  · rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ fun w hw => ?_
    · ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hq⟩, hA⟩
        exact ⟨hq, hA⟩
      · rintro ⟨hq, hA⟩
        exact ⟨⟨Or.inl hA, hq⟩, hA⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      unfold P2
      rw [if_neg hw.2]
  · rw [Finset.filter_filter, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun w hw => ?_
    · ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hk, hq⟩, hA⟩
        exact ⟨hq, keep_inA hk hA⟩
      · rintro ⟨hq, hA'⟩
        exact ⟨⟨Or.inr hA', hq⟩, inA_of_inA' hA'⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      unfold P2
      rw [if_pos (inA_of_inA' hw.2)]
      ring

/-- A kept-set sum over a set disjoint from the operated atom is unchanged. -/
theorem keep_sum_disj (q : C.Ω → Prop) [DecidablePred q] (g : C.Ω → ℝ)
    (hdis : ∀ w, q w → C.hist h w ≠ C.hist h w0) :
    ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ q w), P2 C h w0 w * g w
      = ∑ w ∈ Finset.univ.filter q, C.P w * g w := by
  rw [keep_sum_split]
  have h1 : Finset.univ.filter (fun w => q w ∧ C.hist (h + 1) w = C.hist (h + 1) w0) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hq, hA'⟩
    exact hdis w hq (inA_of_inA' hA')
  have h2 : Finset.univ.filter (fun w => q w ∧ C.hist h w ≠ C.hist h w0)
      = Finset.univ.filter q := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun hq => ⟨hq, hdis w hq⟩⟩
  rw [h1, h2, Finset.sum_empty, mul_zero, add_zero]

/-- A kept-set sum over a set inside the chosen child is scaled by `cc`. -/
theorem keep_sum_in (q : C.Ω → Prop) [DecidablePred q] (g : C.Ω → ℝ)
    (hin : ∀ w, q w → C.hist (h + 1) w = C.hist (h + 1) w0) :
    ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ q w), P2 C h w0 w * g w
      = cc C h w0 * ∑ w ∈ Finset.univ.filter q, C.P w * g w := by
  rw [keep_sum_split]
  have h1 : Finset.univ.filter (fun w => q w ∧ C.hist h w ≠ C.hist h w0) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hq, hA⟩
    exact hA (inA_of_inA' (hin w hq))
  have h2 : Finset.univ.filter (fun w => q w ∧ C.hist (h + 1) w = C.hist (h + 1) w0)
      = Finset.univ.filter q := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun hq => ⟨hq, hin w hq⟩⟩
  rw [h1, h2, Finset.sum_empty, zero_add]

theorem sum_atom_eq_mass_mul (k : ℕ) (g : C.Ω → ℝ) (c : ℝ)
    (hg : ∀ w, C.hist k w = C.hist k w0 → g w = c) :
    ∑ w ∈ Finset.univ.filter (fun w => C.hist k w = C.hist k w0), C.P w * g w
      = C.mass (C.atom k w0) * c := by
  unfold ChunkSystemB.mass ChunkSystemB.atom
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [hg w hw]

/-- A kept-set sum over a set containing the operated atom, of a function constant on
the operated atom, is unchanged. -/
theorem keep_sum_cont (q : C.Ω → Prop) [DecidablePred q] (g : C.Ω → ℝ)
    (hcont : ∀ w, C.hist h w = C.hist h w0 → q w)
    (hg : ∀ w, C.hist h w = C.hist h w0 → g w = g w0) :
    ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ q w), P2 C h w0 w * g w
      = ∑ w ∈ Finset.univ.filter q, C.P w * g w := by
  rw [keep_sum_split]
  have h2 : Finset.univ.filter (fun w => q w ∧ C.hist (h + 1) w = C.hist (h + 1) w0)
      = Finset.univ.filter (fun w => C.hist (h + 1) w = C.hist (h + 1) w0) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun hA' => ⟨hcont w (inA_of_inA' hA'), hA'⟩⟩
  rw [h2, sum_atom_eq_mass_mul (h + 1) g (g w0) (fun w hw => hg w (inA_of_inA' hw)),
    ← mul_assoc, cc_mul, ← sum_atom_eq_mass_mul h g (g w0) hg]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter q)
    (fun w => C.hist h w = C.hist h w0), add_comm, Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hA => ⟨hcont w hA, hA⟩, fun hh => hh.2⟩


theorem keep_sum_univ (g : C.Ω → ℝ)
    (hg : ∀ w, C.hist h w = C.hist h w0 → g w = g w0) :
    ∑ w ∈ Finset.univ.filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0), P2 C h w0 w * g w
      = ∑ w, C.P w * g w := by
  have e := keep_sum_cont (C := C) (h := h) (w0 := w0) (fun _ => True) g (fun _ _ => trivial) hg
  simp only [and_true, Finset.filter_true] at e
  exact e

theorem P2_pos (w : C.Ω) : 0 < P2 C h w0 w := by
  unfold P2
  split_ifs
  · exact mul_pos (C.hP w) cc_pos
  · exact C.hP w

theorem fut2_notA {w : C.Ω} (hA : C.hist h w ≠ C.hist h w0) (k : ℕ) :
    fut2 C h w0 k w = C.futureSize k w := by
  unfold fut2 ChunkSystemB.futureSize
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold size2
  rw [if_neg (fun hh => hA hh.1)]

theorem fut2_gt {w : C.Ω} (hA : C.hist h w = C.hist h w0) {k : ℕ} (hk : h < k) :
    fut2 C h w0 k w = lam C h w0 * C.futureSize k w := by
  unfold fut2 ChunkSystemB.futureSize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  unfold size2
  rw [if_pos ⟨hA, by omega⟩, if_neg (by omega)]

theorem fut2_le {w : C.Ω} (hA : C.hist h w = C.hist h w0) {k : ℕ} (hk : k ≤ h) :
    fut2 C h w0 k w
      = C.futureSize k w - C.futureSize h w + lam C h w0 * C.futureSize (h + 1) w := by
  unfold fut2 ChunkSystemB.futureSize
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold size2
  simp only [hA, true_and]
  split_ifs <;> first | omega | ring1

theorem futdiff_const {w : C.Ω} (hA : C.hist h w = C.hist h w0) {k : ℕ} (hk : k ≤ h) :
    C.futureSize k w - C.futureSize h w = C.futureSize k w0 - C.futureSize h w0 := by
  unfold ChunkSystemB.futureSize
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : h ≤ i.val
  · rw [if_pos (le_trans hk hi), if_pos hi, if_pos (le_trans hk hi), if_pos hi, sub_self, sub_self]
  · have hsz : C.size w i = C.size w0 i :=
      C.hsmeas i w w0 (C.href i h (by omega) w w0 hA)
    rw [if_neg hi, if_neg hi, hsz]

theorem sum_atom_fut (k : ℕ) (u : C.Ω) :
    ∑ w ∈ Finset.univ.filter (fun w => C.hist k w = C.hist k u), C.P w * C.futureSize k w
      = C.mass (C.atom k u) * C.condFuture k u := by
  unfold ChunkSystemB.condFuture ChunkSystemB.condExp
  rw [mul_div_cancel₀ _ (ne_of_gt (C.mass_atom_pos k u))]
  rfl

theorem size2_congr (j : Fin C.m) (w w' : C.Ω) (hh : C.hist j w = C.hist j w') :
    size2 C h w0 w j = size2 C h w0 w' j := by
  unfold size2
  by_cases hj : h ≤ j.val
  · have e : C.hist h w = C.hist h w' := C.href h j hj w w' hh
    rw [e, C.hsmeas j w w' hh]
  · rw [if_neg (fun hh => hj hh.2), if_neg (fun hh => hj hh.2)]
    exact C.hsmeas j w w' hh

theorem size2_mem (hv : C.condFuture h w0 < C.condFuture (h + 1) w0) (w : C.Ω) (j : Fin C.m) :
    0 ≤ size2 C h w0 w j ∧ size2 C h w0 w j ≤ cB := by
  have hs := C.hsize w j
  unfold size2
  split_ifs
  · exact ⟨le_refl 0, le_trans hs.1 hs.2⟩
  · exact ⟨mul_nonneg (lam_nonneg hv) hs.1,
      le_trans (mul_le_of_le_one_left hs.1 (lam_le_one hv)) hs.2⟩
  · exact hs

theorem bc_const {j : Fin C.m} (hjh : j.val < h) {w : C.Ω} (hA : C.hist h w = C.hist h w0)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) :
    E.bailCost bail (((List.ofFn (C.chunk w)).take j).flatten) (C.chunk w j) pe
      = E.bailCost bail (((List.ofFn (C.chunk w0)).take j).flatten) (C.chunk w0 j) pe := by
  have ht : (cl C w).take j = (cl C w0).take j :=
    take_cl_eq C (C.href j h (le_of_lt hjh) w w0 hA)
  have hc : C.chunk w j = C.chunk w0 j :=
    C.hadapt j w w0 (C.href (j + 1) h (by omega) w w0 hA)
  unfold cl at ht
  rw [ht, hc]

theorem hcost2 (hv : C.condFuture h w0 < C.condFuture (h + 1) w0) (hpe : 0 ≤ pe)
    (j : Fin C.m) (u : C.Ω)
    (hu : C.hist h u ≠ C.hist h w0 ∨ C.hist (h + 1) u = C.hist (h + 1) w0)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) :
    size2 C h w0 u j * ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ C.hist j w = C.hist j u), P2 C h w0 w
      ≤ ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ C.hist j w = C.hist j u), P2 C h w0 w *
          E.bailCost bail (((List.ofFn (C.chunk w)).take j).flatten) (C.chunk w j) pe := by
  have e1 := fun (H : ∀ w, C.hist h w = C.hist h w0 → C.hist j w = C.hist j u) =>
    keep_sum_cont (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
      (fun _ => (1 : ℝ)) H (fun _ _ => rfl)
  by_cases H1 : j.val < h ∧ C.hist j u = C.hist j w0
  · have hcont : ∀ w, C.hist h w = C.hist h w0 → C.hist j w = C.hist j u := fun w hw =>
      (C.href j h (le_of_lt H1.1) w w0 hw).trans H1.2.symm
    have hsz : size2 C h w0 u j = C.size u j := by
      unfold size2
      rw [if_neg (fun hh => absurd hh.2 (by omega))]
    have e1' := e1 hcont
    have e2 := keep_sum_cont (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
      (fun w => E.bailCost bail (((List.ofFn (C.chunk w)).take j).flatten) (C.chunk w j) pe)
      hcont (fun w hw => bc_const H1.1 hw E bail)
    simp only [mul_one] at e1'
    beta_reduce at e2
    rw [hsz, e1', e2]
    exact C.hcost j u E bail
  · by_cases H2 : C.hist h u = C.hist h w0
    · have hjh : h ≤ j.val := by
        by_contra hc
        have hc' : j.val < h := lt_of_not_ge hc
        exact H1 ⟨hc', C.href j h (le_of_lt hc') u w0 H2⟩
      rcases eq_or_lt_of_le hjh with hj | hj
      · have hsz : size2 C h w0 u j = 0 := by
          unfold size2
          rw [if_pos ⟨H2, hjh⟩, if_pos hj.symm]
        rw [hsz, zero_mul]
        exact Finset.sum_nonneg fun w _ =>
          mul_nonneg (P2_pos w).le (E.bailCost_nonneg bail _ _ hpe)
      · have hin : ∀ w, C.hist j w = C.hist j u → C.hist (h + 1) w = C.hist (h + 1) w0 :=
          fun w hw => (C.href (h + 1) j hj w u hw).trans (keep_inA hu H2)
        have hsz : size2 C h w0 u j = lam C h w0 * C.size u j := by
          unfold size2
          rw [if_pos ⟨H2, hjh⟩, if_neg (by omega)]
        have e1' := keep_sum_in (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
          (fun _ => (1 : ℝ)) hin
        have e2 := keep_sum_in (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
          (fun w => E.bailCost bail (((List.ofFn (C.chunk w)).take j).flatten) (C.chunk w j) pe)
          hin
        simp only [mul_one] at e1'
        beta_reduce at e2
        rw [hsz, e1', e2]
        have hc := C.hcost j u E bail
        have hM : 0 ≤ ∑ w ∈ Finset.univ.filter (fun w => C.hist j w = C.hist j u), C.P w :=
          Finset.sum_nonneg fun w _ => (C.hP w).le
        have hsm : 0 ≤ C.size u j * ∑ w ∈ Finset.univ.filter
            (fun w => C.hist j w = C.hist j u), C.P w := mul_nonneg (C.hsize u j).1 hM
        have hl1 := lam_le_one hv
        have hl0 := lam_nonneg hv
        have hcc := (cc_pos (C := C) (h := h) (w0 := w0)).le
        calc lam C h w0 * C.size u j * (cc C h w0 * ∑ w ∈ Finset.univ.filter
              (fun w => C.hist j w = C.hist j u), C.P w)
            = cc C h w0 * (lam C h w0 * (C.size u j * ∑ w ∈ Finset.univ.filter
              (fun w => C.hist j w = C.hist j u), C.P w)) := by ring
          _ ≤ cc C h w0 * (C.size u j * ∑ w ∈ Finset.univ.filter
              (fun w => C.hist j w = C.hist j u), C.P w) :=
              mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hsm hl1) hcc
          _ ≤ _ := mul_le_mul_of_nonneg_left hc hcc
    · have hdis : ∀ w, C.hist j w = C.hist j u → C.hist h w ≠ C.hist h w0 := by
        intro w hw hA
        by_cases hjh : j.val ≤ h
        · have hju : C.hist j u = C.hist j w0 := hw.symm.trans (C.href j h hjh w w0 hA)
          rcases eq_or_lt_of_le hjh with hj | hj
          · exact H2 (hj ▸ hju)
          · exact H1 ⟨hj, hju⟩
        · exact H2 ((C.href h j (by omega) u w hw.symm).trans hA)
      have hsz : size2 C h w0 u j = C.size u j := by
        unfold size2
        rw [if_neg (fun hh => H2 hh.1)]
      have e1' := keep_sum_disj (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
        (fun _ => (1 : ℝ)) hdis
      have e2 := keep_sum_disj (C := C) (h := h) (w0 := w0) (fun w => C.hist j w = C.hist j u)
        (fun w => E.bailCost bail (((List.ofFn (C.chunk w)).take j).flatten) (C.chunk w j) pe)
        hdis
      simp only [mul_one] at e1'
      beta_reduce at e2
      rw [hsz, e1', e2]
      exact C.hcost j u E bail

variable (C h w0) in
/-- **One-step surgery** (with a placeholder total): condition the operated atom onto the
chosen child, zero the current chunk there, and scale the child's future by `lam`. -/
noncomputable def surg0 (hv : C.condFuture h w0 < C.condFuture (h + 1) w0) (hpe : 0 ≤ pe) :
    ChunkSystemB X s t 0 cB 0 pe mL where
  Ω := {w : C.Ω // C.hist h w ≠ C.hist h w0 ∨ C.hist (h + 1) w = C.hist (h + 1) w0}
  P := fun w => P2 C h w0 w.1
  m := C.m
  hist := fun k w => C.hist k w.1
  chunk := fun w => C.chunk w.1
  size := fun w j => size2 C h w0 w.1 j
  hP := fun w => P2_pos w.1
  hPsum := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0)) (fun x => by simp) (fun w => P2 C h w0 w)]
    have e := keep_sum_univ (C := C) (h := h) (w0 := w0) (fun _ => (1 : ℝ)) (fun _ _ => rfl)
    simp only [mul_one] at e
    rw [e, C.hPsum]
  hm := C.hm
  hm0 := C.hm0
  href := fun i j hij w w' hh => C.href i j hij w.1 w'.1 hh
  hadapt := fun i w w' hh => C.hadapt i w.1 w'.1 hh
  hsmeas := fun i w w' hh => size2_congr i w.1 w'.1 hh
  hne := fun w i => C.hne w.1 i
  hlast := fun w => C.hlast w.1
  hopt := fun w => C.hopt w.1
  hsize := fun w i => size2_mem hv w.1 i
  hcost := fun i u E bail => by
    have H := hcost2 hv hpe i u.1 u.2 E bail
    rw [← sum_subtype_filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) (fun w => C.hist i w = C.hist i u.1)
        (fun w => P2 C h w0 w)] at H
    rw [← sum_subtype_filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) (fun w => C.hist i w = C.hist i u.1)
        (fun w => P2 C h w0 w *
          E.bailCost bail (((List.ofFn (C.chunk w)).take i).flatten) (C.chunk w i) pe)] at H
    exact H
  htotal := Finset.sum_nonneg fun w _ => mul_nonneg (P2_pos w.1).le
    (Finset.sum_nonneg fun i _ => (size2_mem hv w.1 i).1)

variable (hv : C.condFuture h w0 < C.condFuture (h + 1) w0) (hpe : 0 ≤ pe)

theorem surg0_condFuture (k : ℕ) (u : (surg0 C h w0 hv hpe).Ω) :
    (surg0 C h w0 hv hpe).condFuture k u
      = if C.hist h u.1 = C.hist h w0 ∧ h < k then lam C h w0 * C.condFuture k u.1
        else C.condFuture k u.1 := by
  have hnum : ∑ v ∈ (surg0 C h w0 hv hpe).atom k u,
      (surg0 C h w0 hv hpe).P v * (surg0 C h w0 hv hpe).futureSize k v
      = ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ C.hist k w = C.hist k u.1),
          P2 C h w0 w * fut2 C h w0 k w :=
    sum_subtype_filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) (fun w => C.hist k w = C.hist k u.1)
        (fun w => P2 C h w0 w * fut2 C h w0 k w)
  have hden : (surg0 C h w0 hv hpe).mass ((surg0 C h w0 hv hpe).atom k u)
      = ∑ w ∈ Finset.univ.filter (fun w => (C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) ∧ C.hist k w = C.hist k u.1),
          P2 C h w0 w * 1 := by
    rw [← sum_subtype_filter (fun w => C.hist h w ≠ C.hist h w0 ∨
        C.hist (h + 1) w = C.hist (h + 1) w0) (fun w => C.hist k w = C.hist k u.1)
        (fun w => P2 C h w0 w * 1)]
    simp only [mul_one]
    rfl
  show (∑ v ∈ (surg0 C h w0 hv hpe).atom k u,
      (surg0 C h w0 hv hpe).P v * (surg0 C h w0 hv hpe).futureSize k v)
      / (surg0 C h w0 hv hpe).mass ((surg0 C h w0 hv hpe).atom k u) = _
  rw [hnum, hden]
  have hFdef : C.condFuture k u.1
      = (∑ w ∈ Finset.univ.filter (fun w => C.hist k w = C.hist k u.1),
          C.P w * C.futureSize k w)
        / (∑ w ∈ Finset.univ.filter (fun w => C.hist k w = C.hist k u.1), C.P w * 1) := by
    simp only [mul_one]
    rfl
  by_cases H : C.hist h u.1 = C.hist h w0 ∧ h < k
  · rw [if_pos H]
    have hin : ∀ w, C.hist k w = C.hist k u.1 → C.hist (h + 1) w = C.hist (h + 1) w0 :=
      fun w hw => (C.href (h + 1) k H.2 w u.1 hw).trans (keep_inA u.2 H.1)
    rw [keep_sum_in (fun w => C.hist k w = C.hist k u.1) (fun w => fut2 C h w0 k w) hin,
      keep_sum_in (fun w => C.hist k w = C.hist k u.1) (fun _ => (1 : ℝ)) hin, hFdef]
    have hfut : ∀ w ∈ Finset.univ.filter (fun w => C.hist k w = C.hist k u.1),
        C.P w * fut2 C h w0 k w = lam C h w0 * (C.P w * C.futureSize k w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [fut2_gt (inA_of_inA' (hin w hw)) H.2]
      ring
    rw [Finset.sum_congr rfl hfut, ← Finset.mul_sum,
      mul_div_mul_left _ _ (ne_of_gt (cc_pos (C := C) (h := h) (w0 := w0)))]
    ring
  · rw [if_neg H]
    by_cases H3 : k ≤ h ∧ C.hist k u.1 = C.hist k w0
    · have hcont : ∀ w, C.hist h w = C.hist h w0 → C.hist k w = C.hist k u.1 := fun w hw =>
        (C.href k h H3.1 w w0 hw).trans H3.2.symm
      rw [keep_sum_cont (fun w => C.hist k w = C.hist k u.1) (fun _ => (1 : ℝ)) hcont
        (fun _ _ => rfl), hFdef]
      congr 1
      rw [keep_sum_split]
      beta_reduce
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun w => C.hist k w = C.hist k u.1))
        (fun w => C.hist h w = C.hist h w0) (fun w => C.P w * C.futureSize k w)
      rw [Finset.filter_filter, Finset.filter_filter] at hsplit
      rw [← hsplit]
      have e1 : ∑ w ∈ Finset.univ.filter
            (fun w => C.hist k w = C.hist k u.1 ∧ C.hist h w ≠ C.hist h w0),
            C.P w * fut2 C h w0 k w
          = ∑ w ∈ Finset.univ.filter
            (fun w => C.hist k w = C.hist k u.1 ∧ ¬ C.hist h w = C.hist h w0),
            C.P w * C.futureSize k w := by
        refine Finset.sum_congr rfl fun w hw => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [fut2_notA hw.2]
      rw [e1, add_comm (∑ w ∈ Finset.univ.filter
            (fun w => C.hist k w = C.hist k u.1 ∧ C.hist h w = C.hist h w0),
            C.P w * C.futureSize k w)]
      congr 1
      · have hA' : Finset.univ.filter
            (fun w => C.hist k w = C.hist k u.1 ∧ C.hist (h + 1) w = C.hist (h + 1) w0)
            = Finset.univ.filter (fun w => C.hist (h + 1) w = C.hist (h + 1) w0) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun hh => hh.2, fun hh => ⟨hcont w (inA_of_inA' hh), hh⟩⟩
        have hA : Finset.univ.filter
            (fun w => C.hist k w = C.hist k u.1 ∧ C.hist h w = C.hist h w0)
            = Finset.univ.filter (fun w => C.hist h w = C.hist h w0) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun hh => hh.2, fun hh => ⟨hcont w hh, hh⟩⟩
        rw [hA', hA]
        set G := C.futureSize k w0 - C.futureSize h w0 with hG
        have h1 : ∀ w ∈ Finset.univ.filter (fun w => C.hist (h + 1) w = C.hist (h + 1) w0),
            C.P w * fut2 C h w0 k w
              = C.P w * G + lam C h w0 * (C.P w * C.futureSize (h + 1) w) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          rw [fut2_le (inA_of_inA' hw) H3.1, futdiff_const (inA_of_inA' hw) H3.1]
          ring
        have h2 : ∀ w ∈ Finset.univ.filter (fun w => C.hist h w = C.hist h w0),
            C.P w * C.futureSize k w = C.P w * G + C.P w * C.futureSize h w := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          rw [hG, ← futdiff_const hw H3.1]
          ring
        rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, sum_atom_fut, sum_atom_fut,
          sum_atom_eq_mass_mul (h + 1) (fun _ => G) G (fun _ _ => rfl),
          sum_atom_eq_mass_mul h (fun _ => G) G (fun _ _ => rfl)]
        have hm := cc_mul (C := C) (h := h) (w0 := w0)
        have hl := lam_mul hv
        calc cc C h w0 * (C.mass (C.atom (h + 1) w0) * G
              + lam C h w0 * (C.mass (C.atom (h + 1) w0) * C.condFuture (h + 1) w0))
            = (cc C h w0 * C.mass (C.atom (h + 1) w0)) * G
              + (cc C h w0 * C.mass (C.atom (h + 1) w0))
                * (lam C h w0 * C.condFuture (h + 1) w0) := by ring
          _ = _ := by rw [hm, hl]
    · have hdis : ∀ w, C.hist k w = C.hist k u.1 → C.hist h w ≠ C.hist h w0 := by
        intro w hw hA
        by_cases hkh : k ≤ h
        · exact H3 ⟨hkh, hw.symm.trans (C.href k h hkh w w0 hA)⟩
        · exact H ⟨(C.href h k (by omega) u.1 w hw.symm).trans hA, by omega⟩
      rw [keep_sum_disj (fun w => C.hist k w = C.hist k u.1) (fun w => fut2 C h w0 k w) hdis,
        keep_sum_disj (fun w => C.hist k w = C.hist k u.1) (fun _ => (1 : ℝ)) hdis, hFdef]
      congr 1
      refine Finset.sum_congr rfl fun w hw => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [fut2_notA (hdis w hw)]

theorem surg0_sizeN (k : ℕ) (u : (surg0 C h w0 hv hpe).Ω) :
    (surg0 C h w0 hv hpe).sizeN k u
      = if C.hist h u.1 = C.hist h w0 ∧ h ≤ k then
          (if k = h then 0 else lam C h w0 * C.sizeN k u.1) else C.sizeN k u.1 := by
  unfold ChunkSystemB.sizeN
  show (if hh : k < C.m then size2 C h w0 u.1 ⟨k, hh⟩ else 0) = _
  by_cases hk : k < C.m
  · rw [dif_pos hk, dif_pos hk]
    rfl
  · rw [dif_neg hk, dif_neg hk]
    split_ifs <;> simp

omit hv hpe in
theorem futureSize_zero_eq {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (D : ChunkSystemB X s t cLo cHi total price mLo) (w : D.Ω) :
    D.futureSize 0 w = ∑ i, D.size w i := by
  unfold ChunkSystemB.futureSize
  rw [Finset.filter_true_of_mem (fun i _ => Nat.zero_le _)]

omit hv hpe in
theorem total_eq_sum_condFuture {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (D : ChunkSystemB X s t cLo cHi total price mLo) :
    ∑ w, D.P w * ∑ i, D.size w i = ∑ w, D.P w * D.condFuture 0 w := by
  unfold ChunkSystemB.condFuture
  rw [D.sum_mul_condExp]
  exact Finset.sum_congr rfl fun w _ => by rw [futureSize_zero_eq]

theorem surg0_total :
    ∑ v, (surg0 C h w0 hv hpe).P v * ∑ i, (surg0 C h w0 hv hpe).size v i
      = ∑ w, C.P w * ∑ i, C.size w i := by
  rw [total_eq_sum_condFuture, total_eq_sum_condFuture]
  have e : ∀ v : (surg0 C h w0 hv hpe).Ω,
      (surg0 C h w0 hv hpe).P v * (surg0 C h w0 hv hpe).condFuture 0 v
        = P2 C h w0 v.1 * C.condFuture 0 v.1 := by
    intro v
    rw [surg0_condFuture]
    rw [if_neg (fun hh => absurd hh.2 (Nat.not_lt_zero h))]
    rfl
  rw [Finset.sum_congr rfl fun v _ => e v]
  show ∑ v : {w : C.Ω // C.hist h w ≠ C.hist h w0 ∨ C.hist (h + 1) w = C.hist (h + 1) w0},
    P2 C h w0 v.1 * C.condFuture 0 v.1 = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun w => C.hist h w ≠ C.hist h w0 ∨
      C.hist (h + 1) w = C.hist (h + 1) w0)) (fun x => by simp)
      (fun w => P2 C h w0 w * C.condFuture 0 w)]
  exact keep_sum_univ (C := C) (h := h) (w0 := w0) (fun w => C.condFuture 0 w)
    (fun w hw => C.condFuture_congr (C.href 0 h (Nat.zero_le h) w w0 hw))

omit hv hpe in
theorem djb_iff {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (D : ChunkSystemB X s t cLo cHi total price mLo) (jb : ℝ) :
    D.DoobJumpBound jb ↔
      ∀ k w, |D.sizeN k w + D.condFuture (k + 1) w - D.condFuture k w| ≤ jb := by
  unfold ChunkSystemB.DoobJumpBound
  have e : ∀ k w, D.doobTotal (k + 1) w - D.doobTotal k w
      = D.sizeN k w + D.condFuture (k + 1) w - D.condFuture k w := by
    intro k w
    rw [D.doobTotal_eq_past_add_condFuture, D.doobTotal_eq_past_add_condFuture,
      D.pastSize_succ]
    ring
  simp only [e]

theorem surg0_djb {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) :
    (surg0 C h w0 hv hpe).DoobJumpBound jbS := by
  rw [djb_iff] at hjb ⊢
  intro k u
  rw [surg0_condFuture, surg0_condFuture, surg0_sizeN]
  by_cases hA : C.hist h u.1 = C.hist h w0
  · rcases lt_trichotomy k h with hk | hk | hk
    · rw [if_neg (fun hh => by omega), if_neg (fun hh => by omega),
        if_neg (fun hh => by omega)]
      exact hjb k u.1
    · subst hk
      rw [if_pos ⟨hA, le_refl _⟩, if_pos rfl, if_pos ⟨hA, Nat.lt_succ_self _⟩,
        if_neg (fun hh => absurd hh.2 (lt_irrefl _))]
      have hA' := keep_inA u.2 hA
      rw [C.condFuture_congr hA', C.condFuture_congr hA, lam_mul hv]
      simp only [zero_add, sub_self, abs_zero]
      exact hjb0
    · rw [if_pos ⟨hA, le_of_lt hk⟩, if_neg (by omega), if_pos ⟨hA, by omega⟩, if_pos ⟨hA, hk⟩]
      have e : lam C h w0 * C.sizeN k u.1 + lam C h w0 * C.condFuture (k + 1) u.1
          - lam C h w0 * C.condFuture k u.1
          = lam C h w0 * (C.sizeN k u.1 + C.condFuture (k + 1) u.1 - C.condFuture k u.1) := by
        ring
      rw [e, abs_mul, abs_of_nonneg (lam_nonneg hv)]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (lam_le_one hv)) (hjb k u.1)
  · rw [if_neg (fun hh => hA hh.1), if_neg (fun hh => hA hh.1), if_neg (fun hh => hA hh.1)]
    exact hjb k u.1

omit hv hpe in
/-- The upward moves of the conditional future mass, as (time, outcome) pairs. -/
noncomputable def viol {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (D : ChunkSystemB X s t cLo cHi total price mLo) : Finset (ℕ × D.Ω) :=
  (Finset.range D.m ×ˢ Finset.univ).filter
    (fun p => D.condFuture p.1 p.2 < D.condFuture (p.1 + 1) p.2)

theorem surg0_viol (hmem : (h, w0) ∈ viol C) :
    (viol (surg0 C h w0 hv hpe)).card < (viol C).card := by
  have hle : (viol (surg0 C h w0 hv hpe)).card ≤ ((viol C).erase (h, w0)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.1)) ?_ ?_
    · intro p hp
      simp only [viol, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_univ, and_true, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_erase, viol, Finset.coe_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_univ, and_true, Set.mem_diff, Set.mem_setOf_eq,
        Set.mem_singleton_iff]
      obtain ⟨hpm, hpv⟩ := hp
      rw [surg0_condFuture, surg0_condFuture] at hpv
      by_cases hA : C.hist h p.2.1 = C.hist h w0
      · rcases lt_trichotomy p.1 h with hk | hk | hk
        · rw [if_neg (fun hh => by omega), if_neg (fun hh => by omega)] at hpv
          exact ⟨⟨hpm, hpv⟩, fun hh => by
            have := congrArg Prod.fst hh
            simp at this
            omega⟩
        · exfalso
          rw [if_neg (fun hh => absurd hh.2 (by omega)), if_pos ⟨hA, by omega⟩, hk] at hpv
          have hA' := keep_inA p.2.2 hA
          rw [C.condFuture_congr hA', C.condFuture_congr hA, lam_mul hv] at hpv
          exact lt_irrefl _ hpv
        · rw [if_pos ⟨hA, hk⟩, if_pos ⟨hA, by omega⟩] at hpv
          have hl := lam_nonneg hv
          refine ⟨⟨hpm, ?_⟩, fun hh => by
            have := congrArg Prod.fst hh
            simp at this
            omega⟩
          by_contra hc
          exact absurd hpv (not_lt.mpr (mul_le_mul_of_nonneg_left (not_lt.mp hc) hl))
      · rw [if_neg (fun hh => hA hh.1), if_neg (fun hh => hA hh.1)] at hpv
        refine ⟨⟨hpm, hpv⟩, fun hh => ?_⟩
        have := congrArg Prod.snd hh
        simp at this
        exact hA (by rw [this])
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (Subtype.ext hpq.2)
  exact lt_of_le_of_lt hle (Finset.card_erase_lt_of_mem hmem)

variable (C h w0) in
/-- The one-step surgery with the true total. -/
noncomputable def surg : ChunkSystemB X s t 0 cB T pe mL :=
  { surg0 C h w0 hv hpe with
    htotal := by
      have := surg0_total hv hpe
      rw [this]
      exact C.htotal }

theorem surg_viol (hmem : (h, w0) ∈ viol C) :
    (viol (surg C h w0 hv hpe)).card < (viol C).card :=
  surg0_viol hv hpe hmem

theorem surg_djb {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) :
    (surg C h w0 hv hpe).DoobJumpBound jbS :=
  surg0_djb hv hpe hjb hjb0

theorem surg_total :
    ∑ v, (surg C h w0 hv hpe).P v * ∑ i, (surg C h w0 hv hpe).size v i
      = ∑ w, C.P w * ∑ i, C.size w i :=
  surg0_total hv hpe

end Surgery

section Anti

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}

/-- **Antitonisation.** Repeated one-step surgery removes every upward move of the conditional
future mass, keeping the total, the trivial initial history, nonempty chunks and the jump bound. -/
theorem antitonize {jbS : ℝ} (hjb0 : 0 ≤ jbS) (hpe : 0 ≤ pe) :
    ∀ (n : ℕ) (C : ChunkSystemB X s t 0 cB T pe mL), (viol C).card = n →
    (∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') →
    (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
    C.DoobJumpBound jbS →
    ∃ C1 : ChunkSystemB X s t 0 cB T pe mL,
      (∀ ω ω' : C1.Ω, C1.hist 0 ω = C1.hist 0 ω') ∧
      (∀ (ω : C1.Ω) (i : Fin C1.m), C1.chunk ω i ≠ []) ∧
      C1.DoobJumpBound jbS ∧
      (∑ ω, C1.P ω * ∑ i, C1.size ω i) = (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
      (∀ k ω, C1.condFuture (k + 1) ω ≤ C1.condFuture k ω) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hn h0 hch hjb
  by_cases hV : viol C = ∅
  · refine ⟨C, h0, hch, hjb, rfl, fun k ω => ?_⟩
    by_cases hk : k < C.m
    · by_contra hc
      have hmem : (k, ω) ∈ viol C := by
        simp only [viol, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_univ, and_true]
        exact ⟨hk, lt_of_not_ge hc⟩
      rw [hV] at hmem
      exact Finset.notMem_empty _ hmem
    · rw [C.condFuture_of_m_le (by omega), C.condFuture_of_m_le (by omega)]
  · obtain ⟨⟨h, w0⟩, hmem⟩ := Finset.nonempty_iff_ne_empty.mpr hV
    have hv : C.condFuture h w0 < C.condFuture (h + 1) w0 := (Finset.mem_filter.mp hmem).2
    have hlt : (viol (surg C h w0 hv hpe)).card < n := hn ▸ surg_viol hv hpe hmem
    obtain ⟨C1, h1, h2, h3, h4, h5⟩ := ih _ hlt (surg C h w0 hv hpe) rfl
      (fun ω ω' => h0 ω.1 ω'.1) (fun ω i => hch ω.1 i) (surg_djb hv hpe hjb hjb0)
    exact ⟨C1, h1, h2, h3, h4.trans (surg_total hv hpe), h5⟩

end Anti

end B6cb

end KServer

/-! Step B: regroup an antitone system into `M` windows cut at level crossings. -/

namespace KServer

namespace B6cb

theorem flatten_take_windows {α : Type*} (cs : List (List α)) (τ : ℕ → ℕ) (M : ℕ)
    (h0 : τ 0 = 0) (hmono : ∀ j, j < M → τ j ≤ τ (j + 1)) :
    ∀ j, j ≤ M → ((List.ofFn (fun i : Fin M =>
        ((cs.drop (τ i)).take (τ (i + 1) - τ i)).flatten)).take j).flatten
      = (cs.take (τ j)).flatten := by
  intro j
  induction j with
  | zero => intro _; simp [h0]
  | succ j ih =>
    intro hj
    have hjM : j < M := by omega
    rw [List.take_succ, List.flatten_append, ih (by omega), List.getElem?_ofFn, dif_pos hjM]
    simp only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [← List.flatten_append, ← List.take_add, Nat.add_sub_cancel' (hmono j hjM)]

section Regroup

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t 0 cB T pe mL) (M : ℕ) (a : ℝ)

theorem stop_congr {σ : C.Ω → ℕ} (hσ : C.IsStopping σ) {w w' : C.Ω}
    (hh : C.hist (σ w) w' = C.hist (σ w) w) : σ w' = σ w := by
  have h1 : σ w' ≤ σ w := (hσ (σ w) w w' hh.symm).mp (le_refl _)
  rcases lt_or_eq_of_le h1 with hlt | heq
  · exfalso
    have hh' : C.hist (σ w') w = C.hist (σ w') w' :=
      (C.href (σ w') (σ w) h1 w' w hh).symm
    have := (hσ (σ w') w w' hh').mpr (le_refl _)
    omega
  · exact heq

/-- The total expected size. -/
noncomputable def Stot : ℝ := ∑ w, C.P w * ∑ i, C.size w i

/-- The crossing levels. -/
noncomputable def Lv (j : ℕ) : ℝ := Stot C - j * a

/-- The window boundaries: first times the conditional future mass drops to the levels. -/
noncomputable def tau (j : ℕ) (w : C.Ω) : ℕ :=
  if j < M then C.hitTime (Lv C a j) w else C.m

variable {C M a}

theorem F0_eq (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (w : C.Ω) :
    C.condFuture 0 w = Stot C := by
  have hA : C.atom 0 w = Finset.univ := by
    ext v
    simp only [ChunkSystemB.mem_atom, Finset.mem_univ, iff_true]
    exact h0 v w
  unfold ChunkSystemB.condFuture ChunkSystemB.condExp
  rw [hA]
  have hm : C.mass Finset.univ = 1 := C.hPsum
  rw [hm, div_one]
  unfold Stot
  exact Finset.sum_congr rfl fun v _ => by rw [futureSize_zero_eq]

theorem Lv_succ (j : ℕ) : Lv C a (j + 1) = Lv C a j - a := by
  unfold Lv
  push_cast
  ring

theorem Lv_nonneg (hS : Stot C = M * a) (ha : 0 < a) {j : ℕ} (hj : j ≤ M) :
    0 ≤ Lv C a j := by
  unfold Lv
  rw [hS]
  have : (j : ℝ) ≤ M := by exact_mod_cast hj
  nlinarith

theorem Lv_M (hS : Stot C = M * a) : Lv C a M = 0 := by
  unfold Lv
  rw [hS]
  ring

theorem tau_le_m (hS : Stot C = M * a) (ha : 0 < a) (j : ℕ) (w : C.Ω) :
    tau C M a j w ≤ C.m := by
  unfold tau
  split_ifs with hj
  · exact C.hitTime_le_m (Lv_nonneg hS ha (le_of_lt hj)) w
  · exact le_refl _

theorem tau_stop (hS : Stot C = M * a) (ha : 0 < a) (j : ℕ) :
    C.IsStopping (tau C M a j) := by
  by_cases hj : j < M
  · have hst := C.hitTime_isStopping (Lv_nonneg hS ha (le_of_lt hj))
    intro h w w' hh
    unfold tau
    rw [if_pos hj, if_pos hj]
    exact hst h w w' hh
  · intro h w w' _
    unfold tau
    rw [if_neg hj, if_neg hj]

theorem tau_of_le {j : ℕ} (hj : M ≤ j) (w : C.Ω) : tau C M a j w = C.m := by
  unfold tau
  rw [if_neg (by omega)]

theorem tau_zero (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hM0 : 0 < M) (w : C.Ω) :
    tau C M a 0 w = 0 := by
  unfold tau
  rw [if_pos hM0]
  have h1 : C.condFuture 0 w ≤ Lv C a 0 := by
    rw [F0_eq h0]
    unfold Lv
    simp
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le h1)

theorem F_tau_le (hS : Stot C = M * a) (ha : 0 < a) {j : ℕ} (hj : j ≤ M) (w : C.Ω) :
    C.condFuture (tau C M a j w) w ≤ Lv C a j := by
  by_cases hjM : j < M
  · unfold tau
    rw [if_pos hjM]
    exact C.condFuture_hitTime_le (Lv_nonneg hS ha hj) w
  · have hjM' : j = M := by omega
    rw [tau_of_le (by omega), C.condFuture_of_m_le (le_refl _), hjM', Lv_M hS]

theorem F_tau_ge (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    {j : ℕ} (hj : j ≤ M) (w : C.Ω) :
    Lv C a j - (cB + jbS) ≤ C.condFuture (tau C M a j w) w := by
  by_cases hjM : j < M
  · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [tau_zero h0 (by omega), F0_eq h0]
      unfold Lv
      simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
      linarith
    · set τ := tau C M a j w with hτ
      have hτdef : τ = C.hitTime (Lv C a j) w := by rw [hτ]; unfold tau; rw [if_pos hjM]
      have hτ0 : τ ≠ 0 := by
        intro h0'
        have h1 := C.condFuture_hitTime_le (Lv_nonneg hS ha hj) w
        rw [← hτdef, h0', F0_eq h0] at h1
        unfold Lv at h1
        have : (1 : ℝ) ≤ j := by exact_mod_cast hjpos
        nlinarith
      obtain ⟨τ', hτ'⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
      have hlt : τ' < C.hitTime (Lv C a j) w := by rw [← hτdef]; omega
      have h1 := C.lt_condFuture_of_lt_hitTime hlt
      have h2 := C.le_condFuture_succ hjb τ' w
      have h3 : C.sizeN τ' w ≤ cB := by
        by_cases hm : τ' < C.m
        · exact C.sizeN_le hm w
        · unfold ChunkSystemB.sizeN
          rw [dif_neg hm]
          exact hcB
      rw [hτ']
      linarith
  · have hjM' : j = M := by omega
    rw [tau_of_le (by omega), C.condFuture_of_m_le (le_refl _), hjM', Lv_M hS]
    linarith

theorem F_gt_before (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) {j : ℕ} (hj : j < M) (w : C.Ω) {h' : ℕ}
    (hh : h' ≤ tau C M a j w) : Lv C a (j + 1) < C.condFuture h' w := by
  rw [Lv_succ]
  rcases lt_or_eq_of_le hh with hlt | heq
  · have hτdef : tau C M a j w = C.hitTime (Lv C a j) w := by unfold tau; rw [if_pos hj]
    rw [hτdef] at hlt
    have := C.lt_condFuture_of_lt_hitTime hlt
    linarith
  · rw [heq]
    have := F_tau_ge h0 hS ha hjb hjb0 hcB (le_of_lt hj) w
    linarith

theorem tau_lt (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) {j : ℕ} (hj : j < M) (w : C.Ω) :
    tau C M a j w < tau C M a (j + 1) w := by
  by_contra hc
  have h1 := F_gt_before h0 hS ha hjb hjb0 hcB hd hj w (not_lt.mp hc)
  have h2 := F_tau_le hS ha (show j + 1 ≤ M by omega) w
  linarith

theorem tau_mono (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) {i j : ℕ} (hij : i ≤ j) (w : C.Ω) :
    tau C M a i w ≤ tau C M a j w := by
  by_cases hjM : M ≤ j
  · rw [tau_of_le hjM]
    exact tau_le_m hS ha i w
  · induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih =>
      exact le_trans (ih (by omega)) (le_of_lt (tau_lt h0 hS ha hjb hjb0 hcB hd (by omega) w))

theorem anti_le (hanti : ∀ k ω, C.condFuture (k + 1) ω ≤ C.condFuture k ω) {k k' : ℕ}
    (hk : k ≤ k') (w : C.Ω) : C.condFuture k' w ≤ C.condFuture k w := by
  induction k', hk using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans (hanti n w) ih

variable (C M a)

/-- The new history: the stopped atom at the window start. -/
noncomputable def histR (j : ℕ) (w : C.Ω) : ℕ :=
  Nat.pair (tau C M a j w) (C.hist (tau C M a j w) w)

/-- The window `j` of an outcome, as one chunk. -/
noncomputable def win (j : ℕ) (w : C.Ω) : List (Set X) :=
  (((cl C w).drop (tau C M a j w)).take (tau C M a (j + 1) w - tau C M a j w)).flatten

/-- The mass of window `j`. -/
noncomputable def WM (j : ℕ) (w : C.Ω) : ℝ :=
  ∑ l ∈ Finset.Ico (tau C M a j w) (tau C M a (j + 1) w), C.sizeN l w

/-- The declared size of window `j`: its conditional expected mass given the stopped atom. -/
noncomputable def sizeR (w : C.Ω) (j : ℕ) : ℝ :=
  (∑ v ∈ Finset.univ.filter (fun v => histR C M a j v = histR C M a j w), C.P v * WM C M a j v)
    / (∑ v ∈ Finset.univ.filter (fun v => histR C M a j v = histR C M a j w), C.P v)

variable {C M a}

theorem atomR_eq (hS : Stot C = M * a) (ha : 0 < a) (j : ℕ) (w : C.Ω) :
    Finset.univ.filter (fun v => histR C M a j v = histR C M a j w)
      = C.atom (tau C M a j w) w := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ChunkSystemB.mem_atom, histR,
    Nat.pair_eq_pair]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1] at h2
    exact h2
  · intro hh
    have e := stop_congr C (tau_stop hS ha j) hh
    exact ⟨e, by rw [e]; exact hh⟩

theorem seqR_prefix (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) (hM0 : 0 < M) (w : C.Ω) {j : ℕ} (hj : j ≤ M) :
    ((List.ofFn (fun i : Fin M => win C M a i w)).take j).flatten
      = pre (cl C w) (tau C M a j w) := by
  unfold win pre
  exact flatten_take_windows (cl C w) (fun i => tau C M a i w) M (tau_zero h0 hM0 w)
    (fun i _ => tau_mono h0 hS ha hjb hjb0 hcB hd (Nat.le_succ i) w) j hj

theorem seqR_eq (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) (hM0 : 0 < M) (w : C.Ω) :
    (List.ofFn (fun i : Fin M => win C M a i w)).flatten = (List.ofFn (C.chunk w)).flatten := by
  have e := seqR_prefix h0 hS ha hjb hjb0 hcB hd hM0 w (le_refl M)
  rw [List.take_of_length_le (by simp), tau_of_le (le_refl M)] at e
  rw [e]
  unfold pre
  rw [List.take_of_length_le (by rw [cl_length])]
  rfl

theorem win_ne (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    (w : C.Ω) {j : ℕ} (hj : j < M) : win C M a j w ≠ [] := by
  have hlt := tau_lt h0 hS ha hjb hjb0 hcB hd hj w
  have hle := tau_le_m hS ha (j + 1) w
  unfold win
  rw [window_cons (cl C w) hlt (by rw [cl_length]; exact hle), List.flatten_cons]
  have hm : tau C M a j w < C.m := lt_of_lt_of_le hlt hle
  rw [show sub (cl C w) (tau C M a j w) = C.chunk w ⟨tau C M a j w, hm⟩ from
    sub_cl C w ⟨tau C M a j w, hm⟩]
  intro hnil
  exact hch w _ (List.append_eq_nil_iff.mp hnil).1

theorem win_mem (w : C.Ω) (j : ℕ) (S : Set X) (hS : S ∈ win C M a j w) : S.Nonempty := by
  unfold win at hS
  obtain ⟨x, hx, hSx⟩ := List.mem_flatten.mp hS
  have hx' : x ∈ cl C w := List.mem_of_mem_drop (List.mem_of_mem_take hx)
  unfold cl at hx'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
  exact C.hne w i S hSx

section Bounds

variable {jbS : ℝ} (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (hS : Stot C = M * a)
    (ha : 0 < a) (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    (hd : cB + jbS < a) (hM0 : 0 < M)
include h0 hS ha hjb hjb0 hcB hd hM0

theorem tau_atom {j : ℕ} {w v : C.Ω} (hv : v ∈ C.atom (tau C M a j w) w) :
    tau C M a j v = tau C M a j w :=
  stop_congr C (tau_stop hS ha j) (C.mem_atom.mp hv)

theorem WM_sum (w : C.Ω) {j : ℕ} (hj : j < M) :
    ∑ v ∈ C.atom (tau C M a j w) w, C.P v * WM C M a j v
      = ∑ v ∈ C.atom (tau C M a j w) w, C.P v *
          (C.condFuture (tau C M a j w) v - C.condFuture (tau C M a (j + 1) v) v) := by
  have hos := C.sum_atom_optional_stopping (tau C M a (j + 1)) (tau_stop hS ha (j + 1))
    (tau C M a j w) w
    (fun v hv => by
      rw [← tau_atom h0 hS ha hjb hjb0 hcB hd hM0 hv]
      exact le_of_lt (tau_lt h0 hS ha hjb hjb0 hcB hd hj v))
    C.m (tau_le_m hS ha j w) (fun v _ => tau_le_m hS ha (j + 1) v)
  have e : ∀ v ∈ C.atom (tau C M a j w) w,
      C.P v * (C.condFuture (tau C M a j w) v - C.condFuture (tau C M a (j + 1) v) v)
        = C.P v * C.condFuture (tau C M a j w) v
          - C.P v * C.condFuture (tau C M a (j + 1) v) v := fun v _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hos, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  unfold WM
  rw [tau_atom h0 hS ha hjb hjb0 hcB hd hM0 hv]
  ring

theorem sizeR_bounds (w : C.Ω) {j : ℕ} (hj : j < M) :
    a - (cB + jbS) ≤ sizeR C M a w j ∧ sizeR C M a w j ≤ a + (cB + jbS) := by
  unfold sizeR
  rw [atomR_eq hS ha]
  have hm := C.mass_atom_pos (tau C M a j w) w
  have hmass : (∑ v ∈ C.atom (tau C M a j w) w, C.P v) = C.mass (C.atom (tau C M a j w) w) :=
    rfl
  rw [hmass, WM_sum h0 hS ha hjb hjb0 hcB hd hM0 w hj, le_div_iff₀ hm, div_le_iff₀ hm]
  have hpt : ∀ v ∈ C.atom (tau C M a j w) w,
      a - (cB + jbS) ≤ C.condFuture (tau C M a j w) v - C.condFuture (tau C M a (j + 1) v) v ∧
      C.condFuture (tau C M a j w) v - C.condFuture (tau C M a (j + 1) v) v
        ≤ a + (cB + jbS) := by
    intro v hv
    have e1 := F_tau_le hS ha (le_of_lt hj) v
    have e2 := F_tau_ge h0 hS ha hjb hjb0 hcB (le_of_lt hj) v
    have e3 := F_tau_le hS ha (show j + 1 ≤ M by omega) v
    have e4 := F_tau_ge h0 hS ha hjb hjb0 hcB (show j + 1 ≤ M by omega) v
    rw [tau_atom h0 hS ha hjb hjb0 hcB hd hM0 hv] at e1 e2
    rw [Lv_succ] at e3 e4
    constructor <;> linarith
  unfold ChunkSystemB.mass
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun v hv => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hpt v hv).1 (C.hP v).le
  · exact Finset.sum_le_sum fun v hv => by
      rw [mul_comm (a + (cB + jbS))]
      exact mul_le_mul_of_nonneg_left (hpt v hv).2 (C.hP v).le

theorem hcostR (hanti : ∀ k ω, C.condFuture (k + 1) ω ≤ C.condFuture k ω) {p' : ℝ}
    (hp : pe + (a + (cB + jbS)) ≤ p') (i : Fin M) (w0 : C.Ω) (E : EvaderAlgorithm X)
    (bail : List (Set X) → Bool) :
    sizeR C M a w0 i * ∑ ω ∈ Finset.univ.filter
        (fun ω => histR C M a i ω = histR C M a i w0), C.P ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => histR C M a i ω = histR C M a i w0), C.P ω *
          E.bailCost bail (((List.ofFn (fun j : Fin M => win C M a j ω)).take i).flatten)
            (win C M a i ω) p' := by
  have hsz : sizeR C M a w0 i * ∑ ω ∈ Finset.univ.filter
        (fun ω => histR C M a i ω = histR C M a i w0), C.P ω
      = ∑ v ∈ C.atom (tau C M a i w0) w0, C.P v * WM C M a i v := by
    unfold sizeR
    rw [atomR_eq hS ha]
    exact div_mul_cancel₀ _ (ne_of_gt (C.mass_atom_pos (tau C M a i w0) w0))
  rw [hsz, atomR_eq hS ha]
  have hτ : ∀ v ∈ C.atom (tau C M a i w0) w0, tau C M a i v = tau C M a i w0 :=
    fun v hv => tau_atom h0 hS ha hjb hjb0 hcB hd hM0 hv
  have hge : ∀ v ∈ C.atom (tau C M a i w0) w0, tau C M a i w0 ≤ tau C M a (i + 1) v := by
    intro v hv
    rw [← hτ v hv]
    exact le_of_lt (tau_lt h0 hS ha hjb hjb0 hcB hd i.2 v)
  have hU : ∀ v ∈ C.atom (tau C M a i w0) w0, ∀ h, tau C M a i w0 ≤ h →
      h ≤ tau C M a (i + 1) v → C.condFuture h v ≤ Lv C a i := by
    intro v hv h hh1 _
    refine le_trans (anti_le hanti hh1 v) ?_
    rw [← hτ v hv]
    exact F_tau_le hS ha (le_of_lt i.2) v
  have hL : ∀ v ∈ C.atom (tau C M a i w0) w0,
      Lv C a (i + 1) - (cB + jbS) ≤ C.condFuture (tau C M a (i + 1) v) v :=
    fun v _ => F_tau_ge h0 hS ha hjb hjb0 hcB (show (i : ℕ) + 1 ≤ M by omega) v
  have hR := remaining_le C (tau C M a i w0) w0 (tau C M a (i + 1)) (tau_stop hS ha (i + 1))
    (tau_le_m hS ha (i + 1)) (Lv C a i) (Lv C a (i + 1)) (cB + jbS) hU hL
  have hK : Lv C a i - (Lv C a (i + 1) - (cB + jbS)) ≤ p' - pe := by
    rw [Lv_succ]
    linarith
  have hW := window_cost_ge_mass C (tau C M a i w0) w0 (tau C M a (i + 1))
    (tau_stop hS ha (i + 1)) (tau_le_m hS ha (i + 1)) hge E bail p' _ hK hR
  calc ∑ v ∈ C.atom (tau C M a i w0) w0, C.P v * WM C M a i v
      = ∑ v ∈ C.atom (tau C M a i w0) w0, C.P v *
          ∑ l ∈ Finset.Ico (tau C M a i w0) (tau C M a (i + 1) v), szN C v l := by
        refine Finset.sum_congr rfl fun v hv => ?_
        unfold WM
        rw [hτ v hv]
        rfl
    _ ≤ _ := hW
    _ = _ := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [seqR_prefix h0 hS ha hjb hjb0 hcB hd hM0 v (le_of_lt i.2)]
        unfold win
        rw [hτ v hv]

theorem histR_href (i j : ℕ) (hij : i ≤ j) (w w' : C.Ω)
    (hh : histR C M a j w = histR C M a j w') : histR C M a i w = histR C M a i w' := by
  unfold histR at hh ⊢
  rw [Nat.pair_eq_pair] at hh ⊢
  obtain ⟨h1, h2⟩ := hh
  rw [← h1] at h2
  have hle := tau_mono h0 hS ha hjb hjb0 hcB hd hij w
  have h3 : C.hist (tau C M a i w) w' = C.hist (tau C M a i w) w :=
    (C.href (tau C M a i w) (tau C M a j w) hle w w' h2).symm
  have e := stop_congr C (tau_stop hS ha i) h3
  exact ⟨e.symm, by rw [e]; exact h3.symm⟩

theorem win_adapt (i : ℕ) (w w' : C.Ω)
    (hh : histR C M a (i + 1) w = histR C M a (i + 1) w') : win C M a i w = win C M a i w' := by
  have hi := histR_href h0 hS ha hjb hjb0 hcB hd hM0 i (i + 1) (Nat.le_succ _) w w' hh
  unfold histR at hh hi
  rw [Nat.pair_eq_pair] at hh hi
  obtain ⟨h1, h2⟩ := hh
  obtain ⟨h3, _⟩ := hi
  rw [← h1] at h2
  have ht := take_cl_eq C h2
  unfold win
  rw [← h1, ← h3, ← List.drop_take, ← List.drop_take, ht]

theorem windows_sum (w : C.Ω) :
    ∑ i : Fin M, WM C M a i w = ∑ i : Fin C.m, C.size w i := by
  have key : ∀ J, J ≤ M → ∑ j ∈ Finset.range J, WM C M a j w
      = ∑ l ∈ Finset.Ico (tau C M a 0 w) (tau C M a J w), C.sizeN l w := by
    intro J
    induction J with
    | zero => intro _; simp
    | succ J ih =>
      intro hJ
      rw [Finset.sum_range_succ, ih (by omega)]
      unfold WM
      exact Finset.sum_Ico_consecutive _
        (tau_mono h0 hS ha hjb hjb0 hcB hd (Nat.zero_le J) w)
        (tau_mono h0 hS ha hjb hjb0 hcB hd (Nat.le_succ J) w)
  rw [Fin.sum_univ_eq_sum_range (fun j => WM C M a j w) M, key M (le_refl M),
    tau_zero h0 hM0 w, tau_of_le (le_refl M), ← Finset.range_eq_Ico,
    ← Fin.sum_univ_eq_sum_range (fun l => C.sizeN l w) C.m]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos i.2]

variable (C M a) in
/-- The regrouped system (placeholder total). -/
noncomputable def regroup0 (hanti : ∀ k ω, C.condFuture (k + 1) ω ≤ C.condFuture k ω)
    {cLo' cHi' p' : ℝ} (hlo0 : 0 < cLo') (hlo : cLo' ≤ a - (cB + jbS))
    (hhi : a + (cB + jbS) ≤ cHi') (hp : pe + (a + (cB + jbS)) ≤ p') :
    ChunkSystemB X s t cLo' cHi' 0 p' M where
  Ω := C.Ω
  P := C.P
  m := M
  hist := histR C M a
  chunk := fun w j => win C M a j w
  size := fun w j => sizeR C M a w j
  hP := C.hP
  hPsum := C.hPsum
  hm := le_refl M
  hm0 := hM0
  href := histR_href h0 hS ha hjb hjb0 hcB hd hM0
  hadapt := fun i w w' hh => win_adapt h0 hS ha hjb hjb0 hcB hd hM0 i w w' hh
  hsmeas := fun i w w' hh => by
    show sizeR C M a w i = sizeR C M a w' i
    unfold sizeR
    rw [hh]
  hne := fun w i S hS => win_mem w i S hS
  hlast := fun w => by
    show ((List.ofFn (fun i : Fin M => win C M a i w)).flatten).getLast? = some {t}
    rw [seqR_eq h0 hS ha hjb hjb0 hcB hd hM0 w]
    exact C.hlast w
  hopt := fun w => by
    show evaderOfflineCost s (List.ofFn (fun i : Fin M => win C M a i w)).flatten ≤ dist s t
    rw [seqR_eq h0 hS ha hjb hjb0 hcB hd hM0 w]
    exact C.hopt w
  hsize := fun w i => by
    have b := sizeR_bounds h0 hS ha hjb hjb0 hcB hd hM0 w i.2
    exact ⟨le_trans hlo b.1, le_trans b.2 hhi⟩
  hcost := fun i w0 E bail => hcostR h0 hS ha hjb hjb0 hcB hd hM0 hanti hp i w0 E bail
  htotal := Finset.sum_nonneg fun w _ => mul_nonneg (C.hP w).le
    (Finset.sum_nonneg fun i _ => le_trans hlo0.le
      (le_trans hlo (sizeR_bounds h0 hS ha hjb hjb0 hcB hd hM0 w i.2).1))

theorem regroup0_total (hanti : ∀ k ω, C.condFuture (k + 1) ω ≤ C.condFuture k ω)
    {cLo' cHi' p' : ℝ} (hlo0 : 0 < cLo') (hlo : cLo' ≤ a - (cB + jbS))
    (hhi : a + (cB + jbS) ≤ cHi') (hp : pe + (a + (cB + jbS)) ≤ p') :
    ∑ w, (regroup0 C M a h0 hS ha hjb hjb0 hcB hd hM0 hanti hlo0 hlo hhi hp).P w *
      ∑ i, (regroup0 C M a h0 hS ha hjb hjb0 hcB hd hM0 hanti hlo0 hlo hhi hp).size w i
      = Stot C := by
  set D := regroup0 C M a h0 hS ha hjb hjb0 hcB hd hM0 hanti hlo0 hlo hhi hp with hD
  have e1 : ∀ i : Fin M, ∑ w, D.P w * D.size w i = ∑ w, C.P w * WM C M a i w := by
    intro i
    have := D.sum_mul_condExp (fun w => WM C M a i w) i
    exact this
  calc ∑ w, D.P w * ∑ i, D.size w i
      = ∑ i : Fin M, ∑ w, D.P w * D.size w i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => Finset.mul_sum _ _ _
    _ = ∑ i : Fin M, ∑ w, C.P w * WM C M a i w := Finset.sum_congr rfl fun i _ => e1 i
    _ = ∑ w, C.P w * ∑ i : Fin M, WM C M a i w := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = Stot C := by
        unfold Stot
        exact Finset.sum_congr rfl fun w _ => by
          rw [windows_sum h0 hS ha hjb hjb0 hcB hd hM0 w]

end Bounds

end Regroup

section Final

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}

theorem pe_nonneg (C : ChunkSystemB X s t 0 cB T pe mL)
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) : 0 ≤ pe := by
  haveI : Nonempty X := ⟨s⟩
  let E : EvaderAlgorithm X :=
    { pos := fun l => match l.getLast? with
        | some S => Classical.epsilon (fun x => x ∈ S)
        | none => s
      serves := by
        intro l S hS
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
        exact Classical.epsilon_spec hS }
  obtain ⟨w⟩ : Nonempty C.Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := C.hPsum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  have hc := C.hcost ⟨0, C.hm0⟩ w E (fun _ => true)
  have hbc : ∀ ω : C.Ω, E.bailCost (fun _ => true)
      (((List.ofFn (C.chunk ω)).take (⟨0, C.hm0⟩ : Fin C.m)).flatten)
      (C.chunk ω ⟨0, C.hm0⟩) pe = pe := by
    intro ω
    have hne := hch ω ⟨0, C.hm0⟩
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    have hbt : bailTime (fun _ => true)
        (((List.ofFn (C.chunk ω)).take (⟨0, C.hm0⟩ : Fin C.m)).flatten)
        (C.chunk ω ⟨0, C.hm0⟩) = some 0 := by
      unfold bailTime
      rw [hx]
      simp [List.range_succ_eq_map]
    rw [E.bailCost_of_bail _ _ _ _ hbt]
    simp [EvaderAlgorithm.costOn]
  simp only [hbc] at hc
  have hm := C.mass_atom_pos 0 w
  have hs := (C.hsize w ⟨0, C.hm0⟩).1
  have hsum : ∑ ω ∈ Finset.univ.filter (fun ω => C.hist (⟨0, C.hm0⟩ : Fin C.m) ω
      = C.hist (⟨0, C.hm0⟩ : Fin C.m) w), C.P ω * pe = pe * C.mass (C.atom 0 w) := by
    unfold ChunkSystemB.mass ChunkSystemB.atom
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum] at hc
  have h1 : 0 ≤ C.size w ⟨0, C.hm0⟩ * C.mass (C.atom 0 w) := mul_nonneg hs hm.le
  have h2 : C.size w ⟨0, C.hm0⟩ * C.mass (C.atom 0 w) ≤ pe * C.mass (C.atom 0 w) := hc
  by_contra hneg
  push Not at hneg
  nlinarith

end Final

end B6cb

end KServer

set_option maxHeartbeats 4000000 in
open KServer in
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    ∃ C' : ChunkSystemB X s t cLo' cHi' T p' M,
      C'.m = M ∧ (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by
  have hpe : 0 ≤ pe := B6cb.pe_nonneg C hch
  obtain ⟨C1, h01, hch1, hjb1, htot1, hanti1⟩ :=
    B6cb.antitonize hjb0 hpe _ C rfl h0 hch hjb
  rw [← htot1] at hlo hhi hp
  set S := ∑ ω, C1.P ω * ∑ i, C1.size ω i with hSdef
  set a := S / M with ha_def
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
  have hd : cB + jbS < a := by linarith
  have ha : 0 < a := by linarith
  have hS1 : B6cb.Stot C1 = M * a := by
    show S = M * (S / M)
    field_simp
  refine ⟨{ B6cb.regroup0 C1 M a h01 hS1 ha hjb1 hjb0 hcB hd hM0 hanti1 hlo0 hlo hhi hp with
    htotal := ?_ }, rfl, ?_, ?_⟩
  · rw [B6cb.regroup0_total]
    exact C1.htotal
  · intro w1 w2
    show B6cb.histR C1 M a 0 w1 = B6cb.histR C1 M a 0 w2
    unfold B6cb.histR
    rw [B6cb.tau_zero h01 hM0 w1, B6cb.tau_zero h01 hM0 w2, h01 w1 w2]
  · intro w i
    exact B6cb.win_ne h01 hS1 ha hjb1 hjb0 hcB hd hch1 w i.2
