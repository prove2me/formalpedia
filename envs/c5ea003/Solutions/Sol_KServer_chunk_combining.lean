-- Prove2me | solution 1 for KServer.chunk_combining
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T11:41:41.044111+00:00
-- url     : https://prove2.me/submissions/ce9dc9cf-453e-4532-9102-d87a1ed066c7

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace CombineWork

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t cA cB T pe mL)

/-- The expected total size. -/
noncomputable def expTotal : ℝ := ∑ ω, C.P ω * C.totalSize ω

/-- A stopping time is constant on the atoms of its own stopping level. -/
theorem stopping_const {σ : C.Ω → ℕ} (hσ : C.IsStopping σ) {ω ω' : C.Ω}
    (hh : C.hist (σ ω) ω' = C.hist (σ ω) ω) : σ ω' = σ ω := by
  have h1 : σ ω' ≤ σ ω := (hσ (σ ω) ω ω' hh.symm).mp (le_refl _)
  rcases Nat.lt_or_ge (σ ω') (σ ω) with hlt | hge
  · exfalso
    have h2 := (hσ (σ ω') ω ω'
      (C.href (σ ω') (σ ω) (le_of_lt hlt) ω' ω hh).symm).mpr (le_refl _)
    omega
  · omega

/-- Inequality version of the saturated-set summation engine. -/
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
    simp only [Finset.mem_filter, C.mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hb1]
    · intro hω
      exact ⟨hsat ω₁ hω₁ ω hω, by rw [hω, hb1]⟩
  rw [hfiber]
  exact hfg ω₁ hω₁

/-- Summing `P · condExp f (σ ·)` at a stopping time over everything
recovers the plain weighted sum. -/
theorem sum_stopped_condExp {σ : C.Ω → ℕ} (hσ : C.IsStopping σ) (f : C.Ω → ℝ) :
    ∑ ω, C.P ω * C.condExp f (σ ω) ω = ∑ ω, C.P ω * f ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω))
    (t := Finset.univ.image (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω)))
    (g := fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω))
    (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * C.condExp f (σ ω) ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω))
    (t := Finset.univ.image (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω)))
    (g := fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω))
    (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * f ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨ω₁, _, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : Finset.univ.filter
        (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω) = b)
      = C.atom (σ ω₁) ω₁ := by
    ext ω
    simp only [Finset.mem_filter, C.mem_atom, Finset.mem_univ, true_and]
    constructor
    · intro hω
      rw [← hb1] at hω
      obtain ⟨he, hh⟩ := Nat.pair_eq_pair.mp hω
      rw [he] at hh
      exact hh
    · intro hω
      have hσc : σ ω = σ ω₁ := stopping_const C hσ hω
      rw [← hb1, hσc, hω]
  rw [hfiber]
  have hconst : ∀ ω ∈ C.atom (σ ω₁) ω₁,
      C.condExp f (σ ω) ω = C.condExp f (σ ω₁) ω := by
    intro ω hm
    rw [C.mem_atom] at hm
    rw [stopping_const C hσ hm]
  rw [Finset.sum_congr rfl fun ω hm => by rw [hconst ω hm]]
  exact C.sum_atom_mul_condExp f (σ ω₁) ω₁

end CombineWork

namespace CombineMain

open CombineWork

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}

section Setup

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ)

/-- The descending target levels, uniformly spaced by `expTotal / M`. -/
noncomputable def lvl (n : ℕ) : ℝ :=
  expTotal C - (min n M : ℕ) * (expTotal C / M)

/-- The window boundary stopping times. -/
noncomputable def τ (n : ℕ) (ω : C.Ω) : ℕ := C.hitTime (lvl C M n) ω

/-- The mass of the `i`-th window. -/
noncomputable def winMass (i : ℕ) (ω : C.Ω) : ℝ :=
  ∑ j ∈ Finset.Ico (τ C M i ω) (τ C M (i + 1) ω), C.sizeN j ω

/-- The conditional size of the `i`-th window. -/
noncomputable def wsize (i : ℕ) (ω : C.Ω) : ℝ :=
  C.condExp (winMass C M i) (τ C M i ω) ω

/-- The output history: the boundary time paired with the fine history there. -/
noncomputable def whist (n : ℕ) (ω : C.Ω) : ℕ :=
  Nat.pair (τ C M n ω) (C.hist (τ C M n ω) ω)

/-- The `i`-th output chunk: the input chunks of the `i`-th window,
concatenated. -/
noncomputable def wchunk (ω : C.Ω) (i : ℕ) : List (Set X) :=
  (((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).drop (τ C M i ω)).flatten

/-- The bail-aware cost of serving the rest of window `i` from input-chunk
position `j`, at escape price `p'`. -/
noncomputable def wcost (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (p' : ℝ) (i j : ℕ) (ω : C.Ω) : ℝ :=
  E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
    ((((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).drop j).flatten) p'

/-- The bail rule stays quiet on all complete input chunks in `[a, j)`. -/
def quiet (bail : List (Set X) → Bool) (a j : ℕ) (ω : C.Ω) : Prop :=
  ∀ k, a ≤ k → k < j → ∀ hk : k < C.m,
    bailTime bail (((List.ofFn (C.chunk ω)).take k).flatten)
      (C.chunk ω ⟨k, hk⟩) = none

end Setup

section Proof

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ}

-- Abbreviations
local notation "T0" => expTotal C
local notation "dlt" => expTotal C / M

theorem expTotal_pos (hcA : 0 < cA) : 0 < expTotal C := by
  have hne : (Finset.univ : Finset C.Ω).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have h1 := C.hPsum
    rw [hcon, Finset.sum_empty] at h1
    norm_num at h1
  refine Finset.sum_pos (fun ω _ => ?_) hne
  refine mul_pos (C.hP ω) ?_
  unfold ChunkSystemB.totalSize
  refine Finset.sum_pos (fun i _ => lt_of_lt_of_le hcA (C.hsize ω i).1) ?_
  rw [Finset.univ_nonempty_iff]
  exact ⟨⟨0, C.hm0⟩⟩

theorem lvl_nonneg (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) : 0 ≤ lvl C M n := by
  unfold lvl
  have h1 : ((min n M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.min_le_right n M
  have h2 : (0:ℝ) < M := by exact_mod_cast hM0
  have h3 : 0 ≤ expTotal C := le_of_lt (expTotal_pos hcA)
  have h4 : (M:ℝ) * (expTotal C / M) = expTotal C := by field_simp
  have h5 : 0 ≤ expTotal C / M := div_nonneg h3 (le_of_lt h2)
  nlinarith [mul_le_mul_of_nonneg_right h1 h5]

theorem lvl_zero : lvl C M 0 = expTotal C := by
  unfold lvl
  simp

theorem lvl_le_expTotal (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) :
    lvl C M n ≤ expTotal C := by
  unfold lvl
  have h3 : 0 ≤ expTotal C := le_of_lt (expTotal_pos hcA)
  have h2 : (0:ℝ) < M := by exact_mod_cast hM0
  have h5 : 0 ≤ expTotal C / M := div_nonneg h3 (le_of_lt h2)
  have h6 : (0:ℝ) ≤ ((min n M : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem lvl_anti (hcA : 0 < cA) (hM0 : 0 < M) {n n' : ℕ} (h : n ≤ n') :
    lvl C M n' ≤ lvl C M n := by
  unfold lvl
  have h1 : ((min n M : ℕ) : ℝ) ≤ ((min n' M : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right M h
  have h3 : 0 ≤ expTotal C := le_of_lt (expTotal_pos hcA)
  have h2 : (0:ℝ) < M := by exact_mod_cast hM0
  have h5 : 0 ≤ expTotal C / M := div_nonneg h3 (le_of_lt h2)
  nlinarith [mul_le_mul_of_nonneg_right h1 h5]

theorem lvl_succ_of_lt {n : ℕ} (hn : n < M) :
    lvl C M (n + 1) = lvl C M n - expTotal C / M := by
  unfold lvl
  have h1 : min (n + 1) M = n + 1 := by omega
  have h2 : min n M = n := by omega
  rw [h1, h2]
  push_cast
  ring

theorem lvl_of_M_le {n : ℕ} (hM0 : 0 < M) (hn : M ≤ n) : lvl C M n = 0 := by
  unfold lvl
  have h1 : min n M = M := by omega
  rw [h1]
  have h2 : (M:ℝ) ≠ 0 := by
    have : (0:ℝ) < M := by exact_mod_cast hM0
    linarith
  field_simp
  ring

theorem τ_mono (hcA : 0 < cA) (hM0 : 0 < M) {n n' : ℕ} (h : n ≤ n') (ω : C.Ω) :
    τ C M n ω ≤ τ C M n' ω := by
  unfold τ
  refine Nat.sInf_le ?_
  show C.condFuture (C.hitTime (lvl C M n') ω) ω ≤ lvl C M n
  exact le_trans (C.condFuture_hitTime_le (lvl_nonneg hcA hM0 n') ω)
    (lvl_anti hcA hM0 h)

theorem τ_le_m (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) (ω : C.Ω) :
    τ C M n ω ≤ C.m :=
  C.hitTime_le_m (lvl_nonneg hcA hM0 n) ω

theorem g_zero (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (ω : C.Ω) :
    C.condFuture 0 ω = expTotal C := by
  have hatom : C.atom 0 ω = Finset.univ := by
    ext ω'
    simp [C.mem_atom, h0 ω' ω]
  have hmass : C.mass Finset.univ = 1 := C.hPsum
  unfold ChunkSystemB.condFuture ChunkSystemB.condExp
  rw [hatom, hmass, div_one]
  unfold expTotal
  refine Finset.sum_congr rfl fun ω' _ => ?_
  congr 1
  unfold ChunkSystemB.futureSize ChunkSystemB.totalSize
  congr 1
  ext i
  simp

theorem τ_zero (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') (ω : C.Ω) :
    τ C M 0 ω = 0 := by
  unfold τ ChunkSystemB.hitTime
  have h1 : 0 ∈ {h | C.condFuture h ω ≤ lvl C M 0} := by
    show C.condFuture 0 ω ≤ lvl C M 0
    rw [g_zero h0 ω, lvl_zero]
  exact Nat.le_zero.mp (Nat.sInf_le h1)

theorem τ_last (hcA : 0 < cA) (hM0 : 0 < M) (ω : C.Ω) {n : ℕ} (hn : M ≤ n) :
    τ C M n ω = C.m := by
  have hx := lvl_nonneg (C := C) hcA hM0 n
  have hτm := τ_le_m (C := C) hcA hM0 n ω
  rcases Nat.lt_or_ge (τ C M n ω) C.m with hlt | hge
  · exfalso
    have h1 : C.condFuture (τ C M n ω) ω ≤ 0 :=
      le_trans (C.condFuture_hitTime_le hx ω) (le_of_eq (lvl_of_M_le hM0 hn))
    have h2 := C.lt_condFuture hcA hlt ω
    linarith
  · omega

theorem g_τ_le (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) (ω : C.Ω) :
    C.condFuture (τ C M n ω) ω ≤ lvl C M n :=
  C.condFuture_hitTime_le (lvl_nonneg hcA hM0 n) ω

theorem le_g_τ (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M) (n : ℕ) (ω : C.Ω) :
    lvl C M n - (cB + jbS) ≤ C.condFuture (τ C M n ω) ω := by
  rcases hτ : τ C M n ω with - | k
  · rw [g_zero h0 ω]
    have h1 := lvl_le_expTotal (C := C) hcA hM0 n
    linarith
  · -- τ = k + 1: overshoot bounded by one step
    have hkm : k < C.m := by
      have := τ_le_m (C := C) hcA hM0 n ω
      omega
    have h1 : lvl C M n < C.condFuture k ω := by
      refine C.lt_condFuture_of_lt_hitTime (x := lvl C M n) ?_
      rw [show C.hitTime (lvl C M n) ω = τ C M n ω from rfl, hτ]
      omega
    have h2 := C.le_condFuture_succ hjb k ω
    have h3 := C.sizeN_le hkm ω
    rw [hτ] at *
    linarith
theorem τ_isStopping (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) :
    C.IsStopping (τ C M n) :=
  C.hitTime_isStopping (lvl_nonneg hcA hM0 n)

theorem τ_lt_τ_succ (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M)
    (hslk : cB + jbS < expTotal C / M) {i : ℕ} (hi : i < M) (ω : C.Ω) :
    τ C M i ω < τ C M (i + 1) ω := by
  by_contra hcon
  push_neg at hcon
  have h1 := le_g_τ h0 hjb hjb0 hcA hcAB hM0 i ω
  have h2 := g_τ_le hcA hM0 (i + 1) ω
  have h3 : C.condFuture (τ C M i ω) ω ≤ C.condFuture (τ C M (i + 1) ω) ω :=
    C.condFuture_antitone hjb hjbA hcon ω
  have h4 := lvl_succ_of_lt (C := C) hi
  linarith

/-- The optional-stopping identity for the conditional window size. -/
theorem wsize_eq (hcA : 0 < cA) (hM0 : 0 < M) (i : ℕ) (ω₀ : C.Ω) :
    wsize C M i ω₀ = C.condFuture (τ C M i ω₀) ω₀
      - C.condExp (fun ω => C.condFuture (τ C M (i + 1) ω) ω) (τ C M i ω₀) ω₀ := by
  set a := τ C M i ω₀ with ha_def
  have hstop := τ_isStopping (C := C) hcA hM0 (i + 1)
  have hτc : ∀ ω ∈ C.atom a ω₀, τ C M i ω = a := fun ω hm =>
    stopping_const C (τ_isStopping hcA hM0 i) (C.mem_atom.mp hm)
  have hτge : ∀ ω ∈ C.atom a ω₀, a ≤ τ C M (i + 1) ω := fun ω hm => by
    rw [← hτc ω hm]
    exact τ_mono hcA hM0 (Nat.le_succ i) ω
  have hτle : ∀ ω ∈ C.atom a ω₀, τ C M (i + 1) ω ≤ C.m := fun ω _ =>
    τ_le_m hcA hM0 (i + 1) ω
  have haN : a ≤ C.m := τ_le_m hcA hM0 i ω₀
  have hOS := C.sum_atom_optional_stopping (τ C M (i + 1)) hstop a ω₀ hτge
    C.m haN hτle
  have hwm : ∀ ω ∈ C.atom a ω₀,
      winMass C M i ω = ∑ j ∈ Finset.Ico a (τ C M (i + 1) ω), C.sizeN j ω :=
    fun ω hm => by
      unfold winMass
      rw [hτc ω hm]
  have h1 : ∑ ω ∈ C.atom a ω₀, C.P ω * winMass C M i ω
      = ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture a ω
        - ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture (τ C M (i + 1) ω) ω := by
    rw [Finset.sum_congr rfl fun ω hm => by rw [hwm ω hm], hOS,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω hm => ?_
    ring
  have h2 : ∑ ω ∈ C.atom a ω₀, C.P ω * C.condFuture a ω
      = C.condFuture a ω₀ * C.mass (C.atom a ω₀) := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hm => ?_
    rw [C.condFuture_congr (C.mem_atom.mp hm)]
    ring
  have hmne := ne_of_gt (C.mass_atom_pos a ω₀)
  show (∑ ω ∈ C.atom a ω₀, C.P ω * winMass C M i ω) / C.mass (C.atom a ω₀) = _
  rw [h1, h2, sub_div, mul_div_cancel_right₀ _ hmne]
  rfl

theorem wsize_le (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M) {i : ℕ} (hi : i < M)
    (ω₀ : C.Ω) :
    wsize C M i ω₀ ≤ expTotal C / M + (cB + jbS) := by
  rw [wsize_eq hcA hM0 i ω₀]
  have h1 := g_τ_le hcA hM0 i ω₀
  have h2 : lvl C M (i + 1) - (cB + jbS)
      ≤ C.condExp (fun ω => C.condFuture (τ C M (i + 1) ω) ω) (τ C M i ω₀) ω₀ :=
    C.le_condExp fun ω _ => le_g_τ h0 hjb hjb0 hcA hcAB hM0 (i + 1) ω
  have h4 := lvl_succ_of_lt (C := C) hi
  linarith

theorem le_wsize (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M) {i : ℕ} (hi : i < M)
    (ω₀ : C.Ω) :
    expTotal C / M - (cB + jbS) ≤ wsize C M i ω₀ := by
  rw [wsize_eq hcA hM0 i ω₀]
  have h1 := le_g_τ h0 hjb hjb0 hcA hcAB hM0 i ω₀
  have h2 : C.condExp (fun ω => C.condFuture (τ C M (i + 1) ω) ω) (τ C M i ω₀) ω₀
      ≤ lvl C M (i + 1) :=
    C.condExp_le fun ω _ => g_τ_le hcA hM0 (i + 1) ω
  have h4 := lvl_succ_of_lt (C := C) hi
  linarith

/-- Decoding output-history agreement. -/
theorem whist_pair {n : ℕ} {ω ω' : C.Ω} :
    whist C M n ω = whist C M n ω'
      ↔ τ C M n ω = τ C M n ω' ∧ C.hist (τ C M n ω) ω = C.hist (τ C M n ω) ω' := by
  unfold whist
  rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [← he] at hf
    exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    rw [← he]
    exact ⟨rfl, hf⟩

/-- The output atom at index `n` is the fine atom at the boundary time. -/
theorem whist_atom (hcA : 0 < cA) (hM0 : 0 < M) (n : ℕ) (ω₀ ω : C.Ω) :
    whist C M n ω = whist C M n ω₀
      ↔ C.hist (τ C M n ω₀) ω = C.hist (τ C M n ω₀) ω₀ := by
  rw [whist_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [he] at hf
    exact hf
  · intro hh
    have hτ : τ C M n ω = τ C M n ω₀ :=
      stopping_const C (τ_isStopping hcA hM0 n) hh
    rw [hτ]
    exact ⟨rfl, hh⟩

/-- Output filtration refinement. -/
theorem whist_ref (hcA : 0 < cA) (hM0 : 0 < M) {i j : ℕ} (hij : i ≤ j)
    {ω ω' : C.Ω} (hh : whist C M j ω = whist C M j ω') :
    whist C M i ω = whist C M i ω' := by
  obtain ⟨he, hf⟩ := whist_pair.mp hh
  have hτi : τ C M i ω ≤ τ C M j ω := τ_mono hcA hM0 hij ω
  have hτeq : τ C M i ω' = τ C M i ω :=
    C.hitTime_congr (lvl_nonneg hcA hM0 i) hf.symm hτi
  rw [whist_pair]
  refine ⟨hτeq.symm, ?_⟩
  exact C.href (τ C M i ω) (τ C M j ω) hτi ω ω' hf

/-- Input chunks below an agreed history level agree. -/
theorem chunk_agree {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω')
    {j : Fin C.m} (hj : (j : ℕ) < b) : C.chunk ω j = C.chunk ω' j :=
  C.hadapt j ω ω' (C.href ((j : ℕ) + 1) b (by omega) ω ω' hh)

theorem take_ofFn_agree {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω') :
    (List.ofFn (C.chunk ω)).take b = (List.ofFn (C.chunk ω')).take b := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    have hkb : k < b := by
      simp only [List.length_take, List.length_ofFn] at h1
      omega
    exact chunk_agree hh hkb

/-- Output chunks are adapted: agreement of the output history at `i + 1`
determines the `i`-th window. -/
theorem wchunk_congr (hcA : 0 < cA) (hM0 : 0 < M) {i : ℕ} {ω ω' : C.Ω}
    (hh : whist C M (i + 1) ω = whist C M (i + 1) ω') :
    wchunk C M ω i = wchunk C M ω' i := by
  obtain ⟨he, hf⟩ := whist_pair.mp hh
  have hτi : τ C M i ω ≤ τ C M (i + 1) ω := τ_mono hcA hM0 (Nat.le_succ i) ω
  have hτeq : τ C M i ω' = τ C M i ω :=
    C.hitTime_congr (lvl_nonneg hcA hM0 i) hf.symm hτi
  unfold wchunk
  rw [← he, hτeq, take_ofFn_agree hf]

/-- The flattened output prefix is the flattened input prefix up to the
boundary time. -/
theorem wchunk_prefix (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hcA : 0 < cA) (hM0 : 0 < M) (ω : C.Ω) (i : ℕ) :
    ((List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take i).flatten
      = ((List.ofFn (C.chunk ω)).take (τ C M i ω)).flatten := by
  induction i with
  | zero =>
    rw [τ_zero h0 ω]
    simp
  | succ i ih =>
    by_cases hiM : i < M
    · have htake : (List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take (i + 1)
          = (List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take i
            ++ [wchunk C M ω i] := by
        rw [List.take_succ]
        congr 1
        rw [List.getElem?_eq_getElem (by simp [hiM])]
        simp only [List.getElem_ofFn]
        rfl
      rw [htake, List.flatten_append, ih]
      unfold wchunk
      rw [List.flatten_cons, List.flatten_nil, List.append_nil]
      have hτi : τ C M i ω ≤ τ C M (i + 1) ω := τ_mono hcA hM0 (Nat.le_succ i) ω
      rw [← List.flatten_append]
      congr 1
      have hsplit := List.take_append_drop (τ C M i ω)
        ((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω))
      rw [List.take_take, min_eq_left hτi] at hsplit
      exact hsplit
    · -- i ≥ M: take saturates and τ is capped
      have hM_le_i : M ≤ i := by omega
      have e1 : (List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take (i + 1)
          = (List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take i := by
        rw [List.take_of_length_le (by simp; omega),
          List.take_of_length_le (by simp; omega)]
      rw [e1, ih, τ_last hcA hM0 ω hM_le_i, τ_last hcA hM0 ω (by omega)]

/-- The full output sequence is the input sequence. -/
theorem wchunk_flatten (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hcA : 0 < cA) (hM0 : 0 < M) (ω : C.Ω) :
    (List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).flatten
      = (List.ofFn (C.chunk ω)).flatten := by
  have h1 := wchunk_prefix h0 hcA hM0 ω M
  rw [List.take_of_length_le (by simp)] at h1
  rw [τ_last hcA hM0 ω (le_refl M), List.take_of_length_le (by simp)] at h1
  exact h1

theorem wsize_congr {i : ℕ} {ω ω' : C.Ω}
    (hh : whist C M i ω = whist C M i ω') :
    wsize C M i ω = wsize C M i ω' := by
  obtain ⟨he, hf⟩ := whist_pair.mp hh
  unfold wsize
  rw [← he]
  exact (C.condExp_congr _ hf.symm).symm

theorem take_flatten_succ (ω : C.Ω) {j : ℕ} (hj : j < C.m) :
    ((List.ofFn (C.chunk ω)).take (j + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take j).flatten ++ C.chunk ω ⟨j, hj⟩ := by
  have h1 : (List.ofFn (C.chunk ω)).take (j + 1)
      = (List.ofFn (C.chunk ω)).take j ++ [C.chunk ω ⟨j, hj⟩] := by
    rw [List.take_succ]
    congr 1
    rw [List.getElem?_eq_getElem (by simp [hj])]
    simp only [List.getElem_ofFn]
    rfl
  rw [h1, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem window_cons (hcA : 0 < cA) (hM0 : 0 < M) (ω : C.Ω) {i j : ℕ}
    (hj : j < τ C M (i + 1) ω) :
    (((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).drop j)
      = C.chunk ω ⟨j, lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)⟩
        :: (((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).drop (j + 1)) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)
  have hlen : j < ((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).length := by
    simp only [List.length_take, List.length_ofFn]
    omega
  rw [List.drop_eq_getElem_cons hlen]
  congr 1
  rw [List.getElem_take, List.getElem_ofFn]

/-- Serving an empty remaining window costs nothing. -/
theorem wcost_end (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (p' : ℝ) {i j : ℕ} (ω : C.Ω) (hj : τ C M (i + 1) ω ≤ j) :
    wcost C M E bail p' i j ω = 0 := by
  unfold wcost
  have h1 : (((List.ofFn (C.chunk ω)).take (τ C M (i + 1) ω)).drop j) = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_take, List.length_ofFn]
    omega
  rw [h1]
  show E.bailCost bail _ [].flatten p' = 0
  rw [List.flatten_nil]
  unfold EvaderAlgorithm.bailCost bailTime
  simp only [List.length_nil, List.range_zero, List.find?_nil]
  unfold EvaderAlgorithm.costOn
  rw [List.append_nil, sub_self]

/-- One quiet step: full service of the current chunk plus the rest. -/
theorem wcost_step_no_bail (hcA : 0 < cA) (hM0 : 0 < M)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {i j : ℕ} (ω : C.Ω) (hj : j < τ C M (i + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)⟩) = none) :
    wcost C M E bail p' i j ω
      = E.costOn (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)⟩)
        + wcost C M E bail p' i (j + 1) ω := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)
  unfold wcost
  rw [window_cons hcA hM0 ω hj, List.flatten_cons,
    E.bailCost_append_of_no_bail bail _ _ _ _ hbail,
    ← take_flatten_succ ω hjm]

/-- One bailing step: the escape happens inside the current chunk, and the
higher price is exactly the input price plus the difference. -/
theorem wcost_step_bail (hcA : 0 < cA) (hM0 : 0 < M)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {i j q : ℕ} (ω : C.Ω) (hj : j < τ C M (i + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)⟩) = some q) :
    wcost C M E bail p' i j ω
      = E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)⟩) pe
        + (p' - pe) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ_le_m hcA hM0 (i + 1) ω)
  unfold wcost
  rw [window_cons hcA hM0 ω hj, List.flatten_cons,
    E.bailCost_append_of_bail bail _ _ _ _ hbail,
    E.bailCost_price_of_bail bail _ _ pe p' hbail]

open Classical in
/-- **The charging induction**: from any quiet, in-window position, the
expected remaining window mass is dominated by the expected bail-aware cost
of the remaining window at the output price. -/
theorem charge_claim (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M)
    {p' : ℝ} (hp : pe + (expTotal C / M + (cB + jbS)) ≤ p')
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {i : ℕ} (hi : i < M) (ω₀ : C.Ω) :
    ∀ d j, τ C M i ω₀ ≤ j → C.m ≤ j + d →
    ∑ ω ∈ (C.atom (τ C M i ω₀) ω₀).filter
        (fun ω => j < τ C M (i + 1) ω ∧ quiet C bail (τ C M i ω₀) j ω),
      C.P ω * (∑ k ∈ Finset.Ico j (τ C M (i + 1) ω), C.sizeN k ω)
    ≤ ∑ ω ∈ (C.atom (τ C M i ω₀) ω₀).filter
        (fun ω => j < τ C M (i + 1) ω ∧ quiet C bail (τ C M i ω₀) j ω),
      C.P ω * wcost C M E bail p' i j ω := by
  have hempty : ∀ j, C.m ≤ j →
      (C.atom (τ C M i ω₀) ω₀).filter
        (fun ω => j < τ C M (i + 1) ω ∧ quiet C bail (τ C M i ω₀) j ω) = ∅ := by
    intro j hj
    rw [Finset.filter_eq_empty_iff]
    rintro ω - ⟨h1, -⟩
    have := τ_le_m (C := C) hcA hM0 (i + 1) ω
    omega
  intro d
  induction d with
  | zero =>
    intro j haj hjd
    rw [hempty j (by omega)]
    simp
  | succ d ih =>
    intro j haj hjd
    by_cases hjm : C.m ≤ j
    · rw [hempty j hjm]
      simp
    · push_neg at hjm
      set a := τ C M i ω₀ with ha_def
      set NBW := (C.atom a ω₀).filter
        (fun ω => j < τ C M (i + 1) ω ∧ quiet C bail a j ω) with hNBW_def
      -- members of NBW have their boundary data pinned
      have hmemA : ∀ ω ∈ NBW, C.hist a ω = C.hist a ω₀ := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact C.mem_atom.mp hm.1
      have hτi_mem : ∀ ω ∈ NBW, τ C M i ω = a := by
        intro ω hm
        exact stopping_const C (τ_isStopping hcA hM0 i) (hmemA ω hm)
      -- Step A: peel the current chunk from the window mass
      have hpeel : ∀ ω ∈ NBW,
          ∑ k ∈ Finset.Ico j (τ C M (i + 1) ω), C.sizeN k ω
            = C.sizeN j ω + ∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact Finset.sum_eq_sum_Ico_succ_bot hm.2.1 _
      -- Step B: the input premise at position j over NBW
      have hsat_NBW : ∀ ω ∈ NBW, ∀ ω', C.hist j ω' = C.hist j ω → ω' ∈ NBW := by
        intro ω hm ω' hh
        rw [hNBW_def, Finset.mem_filter] at hm ⊢
        have hA := hm.1
        have hb := hm.2.1
        have hq := hm.2.2
        refine ⟨?_, ?_, ?_⟩
        · rw [C.mem_atom] at hA ⊢
          exact (C.href a j haj ω' ω hh).trans hA
        · have hiff := τ_isStopping (C := C) hcA hM0 (i + 1) j ω ω' hh.symm
          omega
        · intro k hak hkj hk
          have hhk : C.hist k ω' = C.hist k ω := C.href k j (by omega) ω' ω hh
          have hhk1 : C.hist (k + 1) ω' = C.hist (k + 1) ω :=
            C.href (k + 1) j (by omega) ω' ω hh
          rw [take_ofFn_agree hhk, chunk_agree hhk1 (Nat.lt_succ_self k)]
          exact hq k hak hkj hk
      have hprem : ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
          ≤ ∑ ω ∈ NBW, C.P ω *
              E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe := by
        refine sum_saturated_le C j NBW hsat_NBW _ _ fun ω₁ _ => ?_
        have hpre : C.size ω₁ ⟨j, hjm⟩ * C.mass (C.atom j ω₁)
            ≤ ∑ ω' ∈ C.atom j ω₁, C.P ω' *
                E.bailCost bail (((List.ofFn (C.chunk ω')).take j).flatten)
                  (C.chunk ω' ⟨j, hjm⟩) pe := C.hcost ⟨j, hjm⟩ ω₁ E bail
        refine le_trans (le_of_eq ?_) hpre
        unfold ChunkSystemB.mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω' hm' => ?_
        unfold ChunkSystemB.sizeN
        rw [dif_pos hjm, C.hsmeas ⟨j, hjm⟩ ω' ω₁ (C.mem_atom.mp hm')]
        ring
      -- Step C: split by the bail behaviour on the current chunk
      set cond1 : C.Ω → Prop := fun ω =>
        bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, hjm⟩) = none with hcond1_def
      set S1 := NBW.filter (fun ω => cond1 ω ∧ j + 1 < τ C M (i + 1) ω) with hS1_def
      set S2 := NBW.filter (fun ω => cond1 ω ∧ ¬ j + 1 < τ C M (i + 1) ω) with hS2_def
      set S3 := NBW.filter (fun ω => ¬ cond1 ω) with hS3_def
      -- S1 is the next quiet event
      have hS1_eq : S1 = (C.atom a ω₀).filter
          (fun ω => j + 1 < τ C M (i + 1) ω ∧ quiet C bail a (j + 1) ω) := by
        rw [hS1_def, hNBW_def, Finset.filter_filter]
        ext ω
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hA, ⟨hb, hq⟩, hc1, hb1⟩
          refine ⟨hA, hb1, ?_⟩
          intro k hak hkj hk
          rcases Nat.lt_or_ge k j with hkj' | hkj'
          · exact hq k hak hkj' hk
          · have hkeq : k = j := by omega
            subst hkeq
            exact hc1
        · rintro ⟨hA, hb1, hq⟩
          have hc1 : cond1 ω := hq j haj (by omega) hjm
          exact ⟨hA, ⟨by omega, fun k hak hkj hk => hq k hak (by omega) hk⟩, hc1, hb1⟩
      -- generic three-way split of sums over NBW
      have hsplit0 : ∀ f : C.Ω → ℝ, ∑ ω ∈ NBW, f ω
          = (∑ ω ∈ S1, f ω + ∑ ω ∈ S2, f ω) + ∑ ω ∈ S3, f ω := by
        intro f
        have e1 : NBW.filter cond1 = S1 ∪ S2 := by
          rw [hS1_def, hS2_def]
          ext ω
          simp only [Finset.mem_filter, Finset.mem_union]
          tauto
        have hdisj : Disjoint S1 S2 := by
          rw [hS1_def, hS2_def, Finset.disjoint_filter]
          tauto
        rw [← Finset.sum_filter_add_sum_filter_not NBW cond1 f, e1,
          Finset.sum_union hdisj, hS3_def]
      -- boundary facts on the buckets
      have hb_NBW : ∀ ω ∈ NBW, j < τ C M (i + 1) ω := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact hm.2.1
      have hS2_b : ∀ ω ∈ S2, τ C M (i + 1) ω = j + 1 := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        have h2 := hb_NBW ω hm.1
        have h1 := hm.2.2
        omega
      -- Step E: the escape charge on S3
      have hS3_sat : ∀ ω ∈ S3, ∀ ω', C.hist (j + 1) ω' = C.hist (j + 1) ω → ω' ∈ S3 := by
        intro ω hm ω' hh
        rw [hS3_def, Finset.mem_filter] at hm ⊢
        have hhj : C.hist j ω' = C.hist j ω := C.href j (j + 1) (by omega) ω' ω hh
        refine ⟨hsat_NBW ω hm.1 ω' hhj, ?_⟩
        intro hc1'
        apply hm.2
        simp only [hcond1_def] at hc1' ⊢
        rw [take_ofFn_agree hhj.symm, chunk_agree hh.symm (Nat.lt_succ_self j)]
        exact hc1'
      have hS3_charge : ∑ ω ∈ S3, C.P ω *
            (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω)
          ≤ ∑ ω ∈ S3, C.P ω * (p' - pe) := by
        refine sum_saturated_le C (j + 1) S3 hS3_sat _ _ fun ω₁ hm₁ => ?_
        have hm₁' : ω₁ ∈ NBW := by
          rw [hS3_def, Finset.mem_filter] at hm₁
          exact hm₁.1
        have hτi₁ : τ C M i ω₁ = a := hτi_mem ω₁ hm₁'
        have hmem_b : ∀ ω' ∈ C.atom (j + 1) ω₁, j < τ C M (i + 1) ω' := by
          intro ω' hm'
          have hh := C.mem_atom.mp hm'
          have hhj : C.hist j ω' = C.hist j ω₁ := C.href j (j + 1) (by omega) ω' ω₁ hh
          have hiff := τ_isStopping (C := C) hcA hM0 (i + 1) j ω₁ ω' hhj.symm
          have hb₁ := hb_NBW ω₁ hm₁'
          omega
        have hge : ∀ ω' ∈ C.atom (j + 1) ω₁, j + 1 ≤ τ C M (i + 1) ω' :=
          fun ω' hm' => hmem_b ω' hm'
        have hle' : ∀ ω' ∈ C.atom (j + 1) ω₁, τ C M (i + 1) ω' ≤ C.m :=
          fun ω' _ => τ_le_m hcA hM0 (i + 1) ω'
        have hOS := C.sum_atom_optional_stopping (τ C M (i + 1))
          (τ_isStopping hcA hM0 (i + 1)) (j + 1) ω₁ hge C.m (by omega) hle'
        have hgup : ∀ ω' ∈ C.atom (j + 1) ω₁,
            C.condFuture (j + 1) ω' ≤ lvl C M i := by
          intro ω' hm'
          have hh := C.mem_atom.mp hm'
          have hτi' : τ C M i ω' = τ C M i ω₁ :=
            C.hitTime_congr (lvl_nonneg hcA hM0 i) hh
              (by show τ C M i ω₁ ≤ j + 1; omega)
          have h1 : C.condFuture (j + 1) ω' ≤ C.condFuture (τ C M i ω') ω' :=
            C.condFuture_antitone hjb hjbA (by rw [hτi', hτi₁]; omega) ω'
          exact le_trans h1 (g_τ_le hcA hM0 i ω')
        have hgdn : ∀ ω' ∈ C.atom (j + 1) ω₁,
            lvl C M (i + 1) - (cB + jbS) ≤ C.condFuture (τ C M (i + 1) ω') ω' :=
          fun ω' _ => le_g_τ h0 hjb hjb0 hcA hcAB hM0 (i + 1) ω'
        have h1 : ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' *
              (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω'), C.sizeN k ω')
            = ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * C.condFuture (j + 1) ω'
              - ∑ ω' ∈ C.atom (j + 1) ω₁,
                  C.P ω' * C.condFuture (τ C M (i + 1) ω') ω' := by
          rw [hOS, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun ω' _ => ?_
          ring
        rw [h1]
        have h5 := lvl_succ_of_lt (C := C) hi
        have h2 : ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * C.condFuture (j + 1) ω'
            ≤ ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * lvl C M i :=
          Finset.sum_le_sum fun ω' hm' =>
            mul_le_mul_of_nonneg_left (hgup ω' hm') (le_of_lt (C.hP ω'))
        have h3 : ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * (lvl C M (i + 1) - (cB + jbS))
            ≤ ∑ ω' ∈ C.atom (j + 1) ω₁,
                C.P ω' * C.condFuture (τ C M (i + 1) ω') ω' :=
          Finset.sum_le_sum fun ω' hm' =>
            mul_le_mul_of_nonneg_left (hgdn ω' hm') (le_of_lt (C.hP ω'))
        have h4 : ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * lvl C M i
              - ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * (lvl C M (i + 1) - (cB + jbS))
            ≤ ∑ ω' ∈ C.atom (j + 1) ω₁, C.P ω' * (p' - pe) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun ω' hm' => ?_
          have hP' := le_of_lt (C.hP ω')
          have h6 : lvl C M i - (lvl C M (i + 1) - (cB + jbS)) ≤ p' - pe := by
            rw [h5]
            linarith
          calc C.P ω' * lvl C M i - C.P ω' * (lvl C M (i + 1) - (cB + jbS))
              = C.P ω' * (lvl C M i - (lvl C M (i + 1) - (cB + jbS))) := by ring
            _ ≤ C.P ω' * (p' - pe) := mul_le_mul_of_nonneg_left h6 hP'
        linarith
      -- Step F: decompose the cost over the buckets
      have hcost_S12 : ∀ ω ∈ NBW, cond1 ω →
          C.P ω * wcost C M E bail p' i j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * wcost C M E bail p' i (j + 1) ω := by
        intro ω hm hc
        have hb := hb_NBW ω hm
        simp only [hcond1_def] at hc
        rw [wcost_step_no_bail hcA hM0 E bail p' ω hb hc,
          E.bailCost_of_no_bail bail _ _ pe hc]
        ring
      have hcost_S3 : ∀ ω ∈ S3,
          C.P ω * wcost C M E bail p' i j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * (p' - pe) := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        have hb := hb_NBW ω hm.1
        have hc := hm.2
        simp only [hcond1_def] at hc
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
        rw [wcost_step_bail hcA hM0 E bail p' ω hb hq]
        ring
      have hS1_mem : ∀ ω ∈ S1, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS1_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      have hS2_mem : ∀ ω ∈ S2, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      -- Step G: assemble
      have hLHS : ∑ ω ∈ NBW, C.P ω * (∑ k ∈ Finset.Ico j (τ C M (i + 1) ω), C.sizeN k ω)
          = ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
            + ((∑ ω ∈ S1, C.P ω * (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω)
              + ∑ ω ∈ S2, C.P ω * (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω))
              + ∑ ω ∈ S3, C.P ω * (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω)) := by
        rw [Finset.sum_congr rfl fun ω hm => by rw [hpeel ω hm, mul_add],
          Finset.sum_add_distrib,
          hsplit0 (fun ω => C.P ω * (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω))]
      have hRHS : ∑ ω ∈ NBW, C.P ω * wcost C M E bail p' i j ω
          = ∑ ω ∈ NBW, C.P ω * E.bailCost bail
              (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe
            + ((∑ ω ∈ S1, C.P ω * wcost C M E bail p' i (j + 1) ω
              + ∑ ω ∈ S2, C.P ω * wcost C M E bail p' i (j + 1) ω)
              + ∑ ω ∈ S3, C.P ω * (p' - pe)) := by
        rw [hsplit0 (fun ω => C.P ω * wcost C M E bail p' i j ω),
          hsplit0 (fun ω => C.P ω * E.bailCost bail
            (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe)]
        rw [Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS1_mem ω hm).1 (hS1_mem ω hm).2,
          Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS2_mem ω hm).1 (hS2_mem ω hm).2,
          Finset.sum_congr rfl (hcost_S3),
          Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
      rw [hLHS, hRHS]
      -- compare piece by piece
      have hIH : ∑ ω ∈ S1, C.P ω *
            (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω)
          ≤ ∑ ω ∈ S1, C.P ω * wcost C M E bail p' i (j + 1) ω := by
        rw [hS1_eq]
        exact ih (j + 1) (by omega) (by omega)
      have hS2_zero : ∑ ω ∈ S2, C.P ω *
            (∑ k ∈ Finset.Ico (j + 1) (τ C M (i + 1) ω), C.sizeN k ω)
          ≤ ∑ ω ∈ S2, C.P ω * wcost C M E bail p' i (j + 1) ω := by
        refine le_of_eq (Finset.sum_congr rfl fun ω hm => ?_)
        rw [hS2_b ω hm, Finset.Ico_self, Finset.sum_empty,
          wcost_end E bail p' ω (le_of_eq (hS2_b ω hm))]
      linarith [hprem, hIH, hS2_zero, hS3_charge]

/-- The windows partition the input chunk sequence, so the window masses sum
to the total mass. -/
theorem winMass_partition (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hcA : 0 < cA) (hM0 : 0 < M) (ω : C.Ω) :
    ∑ i ∈ Finset.range M, winMass C M i ω = C.totalSize ω := by
  have key : ∀ n, n ≤ M → ∑ i ∈ Finset.range n, winMass C M i ω
      = ∑ j ∈ Finset.Ico (τ C M 0 ω) (τ C M n ω), C.sizeN j ω := by
    intro n
    induction n with
    | zero =>
      intro _
      simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, ih (by omega)]
      unfold winMass
      exact Finset.sum_Ico_consecutive _ (τ_mono hcA hM0 (Nat.zero_le n) ω)
        (τ_mono hcA hM0 (Nat.le_succ n) ω)
  rw [key M (le_refl M), τ_zero h0 ω, τ_last hcA hM0 ω (le_refl M),
    ← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range (fun j => C.sizeN j ω) C.m]
  unfold ChunkSystemB.totalSize
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos k.isLt]

/-- Conditional window sizes preserve the expected total exactly. -/
theorem sum_wsize (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hcA : 0 < cA) (hM0 : 0 < M) :
    ∑ ω, C.P ω * (∑ i ∈ Finset.range M, wsize C M i ω) = expTotal C := by
  have h1 : ∀ ω : C.Ω, C.P ω * (∑ i ∈ Finset.range M, wsize C M i ω)
      = ∑ i ∈ Finset.range M, C.P ω * wsize C M i ω := fun ω => by
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_comm]
  have h2 : ∀ i ∈ Finset.range M, ∑ ω, C.P ω * wsize C M i ω
      = ∑ ω, C.P ω * winMass C M i ω := by
    intro i _
    show ∑ ω, C.P ω * C.condExp (winMass C M i) (τ C M i ω) ω = _
    exact sum_stopped_condExp C (τ_isStopping hcA hM0 i) (winMass C M i)
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  unfold expTotal
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← Finset.mul_sum, winMass_partition h0 hcA hM0 ω]

theorem wchunk_ne (ω : C.Ω) (i : ℕ) : ∀ S ∈ wchunk C M ω i, S.Nonempty := by
  intro S hS
  unfold wchunk at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (C.chunk ω) :=
    List.mem_of_mem_take (List.mem_of_mem_drop hl)
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hl2
  refine C.hne ω k S ?_
  rw [hk]
  exact hSl

/-- The output cost bound, over the fine boundary atom. -/
theorem wcost_bound (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB) (hM0 : 0 < M)
    (hslk : cB + jbS < expTotal C / M)
    {p' : ℝ} (hp : pe + (expTotal C / M + (cB + jbS)) ≤ p')
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {i : ℕ} (hi : i < M) (ω₀ : C.Ω) :
    wsize C M i ω₀ * C.mass (C.atom (τ C M i ω₀) ω₀)
      ≤ ∑ ω ∈ C.atom (τ C M i ω₀) ω₀,
          C.P ω * E.bailCost bail
            (((List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take i).flatten)
            (wchunk C M ω i) p' := by
  classical
  set a := τ C M i ω₀ with ha_def
  have hτmem : ∀ ω ∈ C.atom a ω₀, τ C M i ω = a := fun ω hm =>
    stopping_const C (τ_isStopping hcA hM0 i) (C.mem_atom.mp hm)
  have hL : wsize C M i ω₀ * C.mass (C.atom a ω₀)
      = ∑ ω ∈ C.atom a ω₀, C.P ω * winMass C M i ω := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum, ← C.sum_atom_mul_condExp (winMass C M i) a ω₀]
    refine Finset.sum_congr rfl fun ω hm => ?_
    have he : C.condExp (winMass C M i) a ω = wsize C M i ω₀ := by
      unfold wsize
      exact C.condExp_congr _ (C.mem_atom.mp hm)
    rw [he]
    ring
  have hNBWa : (C.atom a ω₀).filter
      (fun ω => a < τ C M (i + 1) ω ∧ quiet C bail a a ω) = C.atom a ω₀ := by
    rw [Finset.filter_eq_self]
    intro ω hm
    refine ⟨?_, ?_⟩
    · have h2 := τ_lt_τ_succ h0 hjb hjb0 hjbA hcA hcAB hM0 hslk hi ω
      have h3 := hτmem ω hm
      omega
    · intro k hak hka hk
      exact absurd hka (by omega)
  have hclaim := charge_claim h0 hjb hjb0 hjbA hcA hcAB hM0 hp E bail hi ω₀
    C.m a (le_refl a) (by omega)
  rw [hNBWa] at hclaim
  have hwm : ∀ ω ∈ C.atom a ω₀,
      winMass C M i ω = ∑ k ∈ Finset.Ico a (τ C M (i + 1) ω), C.sizeN k ω := by
    intro ω hm
    unfold winMass
    rw [hτmem ω hm]
  have hR : ∀ ω ∈ C.atom a ω₀, wcost C M E bail p' i a ω
      = E.bailCost bail
          (((List.ofFn (fun k : Fin M => wchunk C M ω (k : ℕ))).take i).flatten)
          (wchunk C M ω i) p' := by
    intro ω hm
    have hτω := hτmem ω hm
    have h1 := wchunk_prefix h0 hcA hM0 ω i
    rw [hτω] at h1
    unfold wcost
    rw [h1]
    unfold wchunk
    rw [hτω]
  rw [hL, Finset.sum_congr rfl fun ω hm => by rw [hwm ω hm]]
  refine le_trans hclaim (le_of_eq ?_)
  exact Finset.sum_congr rfl fun ω hm => by rw [hR ω hm]

open Classical in
/-- **The chunk-combining lemma** (BCR Lemma 10, repaired form): a chunk
system with trivial initial knowledge, a Doob jump bound below the size
floor, and expected total `T0` can be regrouped into `M` chunks of
conditional sizes within `(cB + jbS)` of the uniform spacing `T0 / M`,
serving the same request sequence, at any escape price exceeding the input
price by one spacing plus slack. The expected total is preserved exactly. -/
theorem chunk_combining
    (C : ChunkSystemB X s t cA cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ expTotal C / M - (cB + jbS))
    (hhi : expTotal C / M + (cB + jbS) ≤ cHi')
    (hp : pe + (expTotal C / M + (cB + jbS)) ≤ p') :
    Nonempty (ChunkSystemB X s t cLo' cHi' T p' M) := by
  have hslk : cB + jbS < expTotal C / M := by linarith
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := M
    hist := fun n ω => whist C M n ω
    chunk := fun ω i => wchunk C M ω (i : ℕ)
    size := fun ω i => wsize C M (i : ℕ) ω
    hP := C.hP
    hPsum := C.hPsum
    hm := le_refl M
    hm0 := hM0
    href := fun i j hij ω ω' hh => whist_ref hcA hM0 hij hh
    hadapt := fun i ω ω' hh => wchunk_congr hcA hM0 hh
    hsmeas := fun i ω ω' hh => wsize_congr hh
    hne := fun ω i => wchunk_ne ω (i : ℕ)
    hlast := ?_
    hopt := ?_
    hsize := ?_
    hcost := ?_
    htotal := ?_ }⟩
  · -- hlast
    intro ω
    rw [wchunk_flatten h0 hcA hM0 ω]
    exact C.hlast ω
  · -- hopt
    intro ω
    rw [wchunk_flatten h0 hcA hM0 ω]
    exact C.hopt ω
  · -- hsize
    intro ω i
    constructor
    · have := le_wsize h0 hjb hjb0 hcA hcAB hM0 i.isLt ω
      linarith
    · have := wsize_le h0 hjb hjb0 hcA hcAB hM0 i.isLt ω
      linarith
  · -- hcost
    intro i ω₀ E bail
    have hfilter : Finset.univ.filter
        (fun ω => whist C M (i : ℕ) ω = whist C M (i : ℕ) ω₀)
        = C.atom (τ C M (i : ℕ) ω₀) ω₀ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [whist_atom hcA hM0 (i : ℕ) ω₀ ω, C.mem_atom]
    rw [hfilter]
    exact wcost_bound h0 hjb hjb0 hjbA hcA hcAB hM0 hslk hp E bail i.isLt ω₀
  · -- htotal
    have hT : T ≤ expTotal C := C.htotal
    have h1 := sum_wsize h0 hcA hM0
    calc T ≤ expTotal C := hT
      _ = ∑ ω, C.P ω * (∑ i ∈ Finset.range M, wsize C M i ω) := h1.symm
      _ = ∑ ω, C.P ω * (∑ i : Fin M, wsize C M (i : ℕ) ω) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Fin.sum_univ_eq_sum_range (fun i => wsize C M i ω) M]

end Proof

end CombineMain

namespace KServer

/-- Platform-facing restatement with the expected total spelled out. -/
theorem chunk_combining {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    Nonempty (ChunkSystemB X s t cLo' cHi' T p' M) :=
  CombineMain.chunk_combining C h0 hjb hjb0 hjbA hcA hcAB hM0 hlo0 hlo hhi hp

end KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ}
    (C : KServer.ChunkSystemB X s t cA cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    Nonempty (KServer.ChunkSystemB X s t cLo' cHi' T p' M) :=
  KServer.chunk_combining C h0 hjb hjb0 hjbA hcA hcAB hM0 hlo0 hlo hhi hp
