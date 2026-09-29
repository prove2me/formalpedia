-- Prove2me | Definitions.Def_KServer_chunk_stopping
-- name    : KServer_chunk_stopping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T11:08:14.661692+00:00
-- url     : https://prove2.me/theorems/c194cd8b-3ba1-4994-be47-7d0c96e3b175
-- title:
--   Hitting times and optional stopping for the conditional future mass
-- statement:
--   The stopping-time layer over a chunk system with online escapes: the $\mathbb{N}$-indexed size process, the one-step **drift identity** $\mathbb{E}[g_{h+1} \mid \mathcal F_h] = g_h - c_h$ for the conditional future mass $g_h = \mathbb{E}[\sum_{i \ge h} c_i \mid \mathcal F_h]$ with predictable current size $c_h$, the deviation bound $|g_{h+1} - (g_h - c_h)| \le jb$ under a Doob jump bound, monotone descent of $g$ in the regime $jb \le c_{\mathrm{lo}}$, hitting times $\tau_x = \min\{h : g_h \le x\}$ with their stopping-time property and constancy on stopping-level atoms, a fiberwise summation engine for filtration-saturated events, and the **optional stopping identity over a window**: for a bounded stopping time $\sigma \ge a$, averaged over a time-$a$ atom, $\mathbb{E}[g_\sigma] = \mathbb{E}[g_a] - \mathbb{E}[\sum_{a \le j < \sigma} c_j]$. These are the working parts of the chunk-combining lemma in the BCR induction.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 5 (Lemma 10 machinery), repaired form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

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


