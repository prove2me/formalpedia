-- Prove2me | Definitions.Def_KServer_prophecyW2
-- name    : KServer_prophecyW2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T01:21:22.180432+00:00
-- url     : https://prove2.me/theorems/fe463472-ee24-4d12-86b8-d0a687c0201d
-- title:
--   Sub-probability weights and weighted interval energy
-- statement:
--   Weighted prophecy tools. ProphecyBoundW.sub: the adapted-shift bound serves sub-probability weight families (padding the deficit onto one shift only increases the mixture, since energies are nonnegative). weighted_interval_energy: with a nonnegative weight measurable at the interval's start, the weighted energy of the Doob increments of a function across a depth interval is at most the weighted centred second moment of the function, by the weighted one-step second-moment growth (the cross term vanishes because the weight times the running conditional is measurable at each step), telescoping, conditional Jensen and the tower property. These are the two tools the race's coin-phase prophecy analysis uses per cell of a weighted shifted partition.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2
import Definitions.Def_KServer_prophecyW

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- The adapted-shift bound also serves sub-probability weight
families: padding the deficit onto one shift only increases the
mixture. -/
theorem ProphecyBoundW.sub {κsh : ℕ} {PE : ℝ}
    (h : C.ProphecyBoundW κsh PE)
    (K : ℕ) (e : ℕ → ℕ) (he0 : e 0 = 0) (hem : ∀ k, e k ≤ e (k + 1))
    (heK : e K = C.m) (W : ℕ → C.Ω → ℝ)
    (hW0 : ∀ c (ω : C.Ω), 0 ≤ W c ω)
    (hWm : ∀ c (ω ω' : C.Ω), C.hist κsh ω' = C.hist κsh ω →
      W c ω' = W c ω)
    (hW1 : ∀ ω : C.Ω, ∑ c ∈ Finset.range (κsh + 1), W c ω ≤ 1) :
    ∑ c ∈ Finset.range (κsh + 1), ∑ k ∈ Finset.range K,
      ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
        ∑ ω, C.P ω * W c ω
          * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2 ≤ PE := by
  set W' : ℕ → C.Ω → ℝ := fun c ω =>
    if c = 0 then W c ω + (1 - ∑ c' ∈ Finset.range (κsh + 1), W c' ω)
    else W c ω with hW'
  have hW'0 : ∀ c (ω : C.Ω), 0 ≤ W' c ω := by
    intro c ω
    simp only [hW']
    by_cases hc : c = 0
    · rw [if_pos hc]
      have h1 := hW1 ω
      have h2 := hW0 c ω
      have h3 : 0 ≤ 1 - ∑ c' ∈ Finset.range (κsh + 1), W c' ω := by
        linarith
      have h4 := hW0 0 ω
      subst hc
      linarith
    · rw [if_neg hc]
      exact hW0 c ω
  have hW'm : ∀ c (ω ω' : C.Ω), C.hist κsh ω' = C.hist κsh ω →
      W' c ω' = W' c ω := by
    intro c ω ω' hh
    simp only [hW']
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos hc, hWm c ω ω' hh]
      congr 2
      refine Finset.sum_congr rfl fun c' _ => ?_
      exact hWm c' ω ω' hh
    · rw [if_neg hc, if_neg hc]
      exact hWm c ω ω' hh
  have hpeel : ∀ V : ℕ → ℝ, ∑ c ∈ Finset.range (κsh + 1), V c
      = V 0 + ∑ c ∈ Finset.Ico 1 (κsh + 1), V c := by
    intro V
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega) V]
  have hW'1 : ∀ ω : C.Ω, ∑ c ∈ Finset.range (κsh + 1), W' c ω = 1 := by
    intro ω
    rw [hpeel (fun c => W' c ω)]
    have h1 : W' 0 ω = W 0 ω
        + (1 - ∑ c' ∈ Finset.range (κsh + 1), W c' ω) := by
      simp [hW']
    have h2 : ∑ c ∈ Finset.Ico 1 (κsh + 1), W' c ω
        = ∑ c ∈ Finset.Ico 1 (κsh + 1), W c ω := by
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Finset.mem_Ico] at hc
      simp only [hW']
      rw [if_neg (by omega)]
    rw [h1, h2, hpeel (fun c => W c ω)]
    ring
  have h1 := h K e he0 hem heK W' hW'0 hW'm hW'1
  refine le_trans ?_ h1
  refine Finset.sum_le_sum fun c _ => ?_
  refine Finset.sum_le_sum fun k _ => ?_
  refine Finset.sum_le_sum fun h' _ => ?_
  refine Finset.sum_le_sum fun ω _ => ?_
  have hWle : W c ω ≤ W' c ω := by
    simp only [hW']
    by_cases hc : c = 0
    · rw [if_pos hc]
      have h2 := hW1 ω
      subst hc
      linarith
    · rw [if_neg hc]
  have hnn : (0 : ℝ) ≤ C.P ω
      * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2 :=
    mul_nonneg (le_of_lt (C.hP ω)) (sq_nonneg _)
  nlinarith [hWle, hnn]

/-- **Weighted interval energy**: with a nonnegative weight measurable
at the interval's start, the weighted energy of the Doob increments
across the interval is at most the weighted centred second moment. -/
theorem weighted_interval_energy (f : C.Ω → ℝ) (Wt : C.Ω → ℝ)
    {a b : ℕ} (hab : a ≤ b) (c₀ : ℝ)
    (hWt0 : ∀ ω, 0 ≤ Wt ω)
    (hWtm : ∀ ω ω' : C.Ω, C.hist a ω' = C.hist a ω → Wt ω' = Wt ω) :
    ∑ h ∈ Finset.Ico a b, ∑ ω, C.P ω * Wt ω * (C.dinc f h ω) ^ 2
      ≤ ∑ ω, C.P ω * Wt ω * (f ω - c₀) ^ 2 := by
  set g : C.Ω → ℝ := fun ω => f ω - c₀ with hg
  have hdg : ∀ (h : ℕ) (ω : C.Ω), C.dinc g h ω = C.dinc f h ω := by
    intro h ω
    unfold ChunkSystemB.dinc
    simp only [hg]
    rw [C.condExp_sub f (fun _ => c₀) (h + 1) ω,
      C.condExp_sub f (fun _ => c₀) h ω, C.condExp_const, C.condExp_const]
    ring
  rw [Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun ω _ => by
    rw [← hdg h ω]]
  -- weighted one-step second moment growth
  have hstep : ∀ h, a ≤ h →
      ∑ ω, C.P ω * Wt ω * (C.condExp g (h + 1) ω) ^ 2
      = (∑ ω, C.P ω * Wt ω * (C.condExp g h ω) ^ 2)
        + ∑ ω, C.P ω * Wt ω * (C.dinc g h ω) ^ 2 := by
    intro h hah
    have hcross : ∑ ω, C.P ω
        * ((Wt ω * C.condExp g h ω) * C.dinc g h ω) = 0 := by
      have hu : ∀ ω ω' : C.Ω, C.hist h ω' = C.hist h ω →
          Wt ω' * C.condExp g h ω' = Wt ω * C.condExp g h ω := by
        intro ω ω' hh
        rw [hWtm ω ω' (C.href a h hah ω' ω hh), C.condExp_congr g hh]
      rw [sum_P_mul_condExp h (fun ω => Wt ω * C.condExp g h ω)
        (C.dinc g h) hu]
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [condExp_dinc_zero g h ω]
      ring
    have hexp : ∀ ω : C.Ω, C.P ω * Wt ω * (C.condExp g (h + 1) ω) ^ 2
        = C.P ω * Wt ω * (C.condExp g h ω) ^ 2
          + C.P ω * Wt ω * (C.dinc g h ω) ^ 2
          + 2 * (C.P ω * ((Wt ω * C.condExp g h ω) * C.dinc g h ω)) := by
      intro ω
      have h2 : C.condExp g (h + 1) ω = C.condExp g h ω + C.dinc g h ω := by
        unfold ChunkSystemB.dinc
        ring
      rw [h2]
      ring
    rw [Finset.sum_congr rfl fun ω _ => hexp ω, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
    ring
  have htel : ∀ d : ℕ, ∑ h ∈ Finset.Ico a (a + d),
      ∑ ω, C.P ω * Wt ω * (C.dinc g h ω) ^ 2
      = (∑ ω, C.P ω * Wt ω * (C.condExp g (a + d) ω) ^ 2)
        - ∑ ω, C.P ω * Wt ω * (C.condExp g a ω) ^ 2 := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 from by omega,
        Finset.sum_Ico_succ_top (by omega), ih, hstep (a + d) (by omega)]
      ring
  have hb : b = a + (b - a) := by omega
  rw [hb, htel (b - a)]
  have hlow : 0 ≤ ∑ ω, C.P ω * Wt ω * (C.condExp g a ω) ^ 2 :=
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (mul_nonneg (le_of_lt (C.hP ω)) (hWt0 ω)) (sq_nonneg _)
  have hjen : ∑ ω, C.P ω * Wt ω * (C.condExp g (a + (b - a)) ω) ^ 2
      ≤ ∑ ω, C.P ω * Wt ω * g ω ^ 2 := by
    set d' := a + (b - a) with hd'
    have h1 : ∀ ω : C.Ω, (C.condExp g d' ω) ^ 2
        ≤ C.condExp (fun ω' => g ω' ^ 2) d' ω := by
      intro ω
      unfold ChunkSystemB.condExp
      set A' := C.atom d' ω with hA'
      have hm : 0 < C.mass A' := C.mass_atom_pos d' ω
      rw [div_pow, div_le_div_iff₀ (by positivity) hm]
      have hCS : (∑ ω' ∈ A', Real.sqrt (C.P ω')
            * (Real.sqrt (C.P ω') * g ω')) ^ 2
          ≤ (∑ ω' ∈ A', Real.sqrt (C.P ω') ^ 2)
            * ∑ ω' ∈ A', (Real.sqrt (C.P ω') * g ω') ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq A' _ _
      have e1 : ∀ ω' ∈ A', Real.sqrt (C.P ω')
          * (Real.sqrt (C.P ω') * g ω') = C.P ω' * g ω' := by
        intro ω' _
        rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (C.hP ω'))]
      have e2 : ∀ ω' ∈ A', Real.sqrt (C.P ω') ^ 2 = C.P ω' := by
        intro ω' _
        rw [Real.sq_sqrt (le_of_lt (C.hP ω'))]
      have e3 : ∀ ω' ∈ A', (Real.sqrt (C.P ω') * g ω') ^ 2
          = C.P ω' * g ω' ^ 2 := by
        intro ω' _
        rw [mul_pow, Real.sq_sqrt (le_of_lt (C.hP ω'))]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
        Finset.sum_congr rfl e3] at hCS
      have hnn : 0 ≤ ∑ ω' ∈ A', C.P ω' * g ω' ^ 2 :=
        Finset.sum_nonneg fun ω' _ =>
          mul_nonneg (le_of_lt (C.hP ω')) (sq_nonneg _)
      have hCS' : (∑ ω' ∈ A', C.P ω' * g ω') ^ 2
          ≤ C.mass A' * ∑ ω' ∈ A', C.P ω' * g ω' ^ 2 := hCS
      nlinarith [hCS', hm, hnn]
    have h2 : ∑ ω, C.P ω * Wt ω * (C.condExp g d' ω) ^ 2
        ≤ ∑ ω, C.P ω * Wt ω * C.condExp (fun ω' => g ω' ^ 2) d' ω := by
      refine Finset.sum_le_sum fun ω _ => ?_
      exact mul_le_mul_of_nonneg_left (h1 ω)
        (mul_nonneg (le_of_lt (C.hP ω)) (hWt0 ω))
    refine le_trans h2 (le_of_eq ?_)
    have hu : ∀ ω ω' : C.Ω, C.hist d' ω' = C.hist d' ω →
        Wt ω' = Wt ω := by
      intro ω ω' hh
      exact hWtm ω ω' (C.href a d' (by omega) ω' ω hh)
    have h3 := sum_P_mul_condExp (C := C) d' Wt
      (fun ω' => g ω' ^ 2) hu
    rw [Finset.sum_congr rfl fun ω _ =>
        show C.P ω * Wt ω * C.condExp (fun ω' => g ω' ^ 2) d' ω
          = C.P ω * (Wt ω * C.condExp (fun ω' => g ω' ^ 2) d' ω)
        from by ring, ← h3]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  have hfin : ∀ ω : C.Ω, C.P ω * Wt ω * g ω ^ 2
      = C.P ω * Wt ω * (f ω - c₀) ^ 2 := by
    intro ω
    simp only [hg]
  rw [Finset.sum_congr rfl fun ω _ => (hfin ω).symm]
  linarith

end ChunkSystemB



end KServer


