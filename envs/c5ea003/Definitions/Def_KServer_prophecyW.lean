-- Prove2me | Definitions.Def_KServer_prophecyW
-- name    : KServer_prophecyW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T01:03:54.425521+00:00
-- url     : https://prove2.me/theorems/355dc32e-c0e2-4081-8d99-8bc495128d30
-- title:
--   Adapted-shift prophecy bound
-- statement:
--   The adapted-shift prophecy bound. ProphecyBoundW kappa_sh PE strengthens the partitioned prophecy energy bound: for every partition and every family of nonnegative shift weights (measurable in the depth-kappa_sh history, summing to one over shifts c <= kappa_sh), the weighted mixture of the c-shifted partition prophecy energies (windows [c + e_k, c + e_{k+1}), tails cut at c + e_{k+1}) is at most PE. This is the form of the invariant that survives the race construction: the survivor phase reveals the selected side along windows shifted by the consumed coin count, which is correlated with the side path only through its first kappa chunks, so the race's tail phase consumes exactly one adapted-shift instance of each side's invariant. The plain bound is the delta-at-zero instance (toPlain); the bound weakens in the constant (mono) and descends to smaller shift depths (anti).
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

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- **Adapted-shift prophecy bound**: for every partition and every
family of nonnegative shift weights — measurable in the depth-`κsh`
history, summing to one over shifts `c ≤ κsh` — the weighted mixture of
the `c`-shifted partition prophecy energies is at most `PE`.  The
shifted instance uses windows `[c + e_k, c + e_{k+1})` with tails cut
at `c + e_{k+1}`.  This is the form of the prophecy invariant that
survives the race: the side windows of the survivor phase are shifted
by the consumed coin count, which is correlated with the side path only
through its first `κsh` chunks. -/
def ProphecyBoundW (C : ChunkSystemB X s t cLo cHi total price mLo)
    (κsh : ℕ) (PE : ℝ) : Prop :=
  ∀ (K : ℕ) (e : ℕ → ℕ), e 0 = 0 → (∀ k, e k ≤ e (k + 1)) → e K = C.m →
  ∀ W : ℕ → C.Ω → ℝ,
    (∀ c (ω : C.Ω), 0 ≤ W c ω) →
    (∀ c (ω ω' : C.Ω), C.hist κsh ω' = C.hist κsh ω → W c ω' = W c ω) →
    (∀ ω : C.Ω, ∑ c ∈ Finset.range (κsh + 1), W c ω = 1) →
    ∑ c ∈ Finset.range (κsh + 1), ∑ k ∈ Finset.range K,
      ∑ h ∈ Finset.Ico (c + e k) (c + e (k + 1)),
        ∑ ω, C.P ω * W c ω
          * (C.dinc (C.tailSum (c + e (k + 1))) h ω) ^ 2 ≤ PE

/-- The adapted-shift bound weakens in the constant. -/
theorem ProphecyBoundW.mono {κsh : ℕ} {PE PE' : ℝ}
    (h : C.ProphecyBoundW κsh PE) (hPE : PE ≤ PE') :
    C.ProphecyBoundW κsh PE' :=
  fun K e he0 hem heK W hW0 hWm hW1 =>
    le_trans (h K e he0 hem heK W hW0 hWm hW1) hPE

/-- The adapted-shift bound recovers the plain prophecy bound. -/
theorem ProphecyBoundW.toPlain {κsh : ℕ} {PE : ℝ}
    (h : C.ProphecyBoundW κsh PE) : C.ProphecyBound PE := by
  intro K e he0 hem heK
  set W : ℕ → C.Ω → ℝ := fun c _ => if c = 0 then (1 : ℝ) else 0
    with hW
  have h1 := h K e he0 hem heK W
    (fun c ω => by
      simp only [hW]
      by_cases hc : c = 0
      · rw [if_pos hc]
        norm_num
      · rw [if_neg hc])
    (fun c ω ω' _ => rfl)
    (fun ω => by
      simp only [hW]
      rw [Finset.sum_ite_eq' (Finset.range (κsh + 1)) 0 fun _ => (1 : ℝ),
        if_pos (Finset.mem_range.mpr (by omega))])
  refine le_trans (le_of_eq ?_) h1
  have hz : ∀ c ∈ Finset.range (κsh + 1), c ≠ 0 →
      (∑ k ∈ Finset.range K,
        ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
          ∑ ω, C.P ω * W c ω
            * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2) = 0 := by
    intro c _ hc
    refine Finset.sum_eq_zero fun k _ => ?_
    refine Finset.sum_eq_zero fun h' _ => ?_
    refine Finset.sum_eq_zero fun ω _ => ?_
    simp only [hW]
    rw [if_neg hc]
    ring
  rw [Finset.sum_eq_single 0 hz
    (fun hc => absurd (Finset.mem_range.mpr (by omega)) hc)]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr (by simp) fun h' _ => ?_
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [hW]

/-- The adapted-shift bound descends to smaller shift depths. -/
theorem ProphecyBoundW.anti {κsh κsh' : ℕ} {PE : ℝ}
    (hk : κsh' ≤ κsh) (h : C.ProphecyBoundW κsh PE) :
    C.ProphecyBoundW κsh' PE := by
  intro K e he0 hem heK W hW0 hWm hW1
  set W' : ℕ → C.Ω → ℝ := fun c ω => if c ≤ κsh' then W c ω else 0
    with hW'
  have h1 := h K e he0 hem heK W'
    (fun c ω => by
      simp only [hW']
      by_cases hc : c ≤ κsh'
      · rw [if_pos hc]
        exact hW0 c ω
      · rw [if_neg hc])
    (fun c ω ω' hh => by
      simp only [hW']
      by_cases hc : c ≤ κsh'
      · rw [if_pos hc, if_pos hc]
        exact hWm c ω ω' (C.href κsh' κsh hk ω' ω hh)
      · rw [if_neg hc, if_neg hc])
    (fun ω => by
      rw [show ∑ c ∈ Finset.range (κsh + 1), W' c ω
          = (∑ c ∈ Finset.range (κsh' + 1), W' c ω)
            + ∑ c ∈ Finset.Ico (κsh' + 1) (κsh + 1), W' c ω from by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le (κsh' + 1))
            (show κsh' + 1 ≤ κsh + 1 by omega)]]
      have ha : ∑ c ∈ Finset.range (κsh' + 1), W' c ω
          = ∑ c ∈ Finset.range (κsh' + 1), W c ω := by
        refine Finset.sum_congr rfl fun c hc => ?_
        simp only [Finset.mem_range] at hc
        simp only [hW']
        rw [if_pos (by omega)]
      have hb : ∑ c ∈ Finset.Ico (κsh' + 1) (κsh + 1), W' c ω = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        simp only [Finset.mem_Ico] at hc
        simp only [hW']
        rw [if_neg (by omega)]
      rw [ha, hb, add_zero, hW1 ω])
  refine le_trans (le_of_eq ?_) h1
  rw [show ∑ c ∈ Finset.range (κsh + 1), ∑ k ∈ Finset.range K,
      ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
        ∑ ω, C.P ω * W' c ω
          * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2
      = (∑ c ∈ Finset.range (κsh' + 1), ∑ k ∈ Finset.range K,
          ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
            ∑ ω, C.P ω * W' c ω
              * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2)
        + ∑ c ∈ Finset.Ico (κsh' + 1) (κsh + 1), ∑ k ∈ Finset.range K,
            ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
              ∑ ω, C.P ω * W' c ω
                * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2 from by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (κsh' + 1))
            (show κsh' + 1 ≤ κsh + 1 by omega)]
    congr 1
    rw [Finset.range_eq_Ico]]
  have ha : ∑ c ∈ Finset.range (κsh' + 1), ∑ k ∈ Finset.range K,
      ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
        ∑ ω, C.P ω * W' c ω
          * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2
      = ∑ c ∈ Finset.range (κsh' + 1), ∑ k ∈ Finset.range K,
        ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
          ∑ ω, C.P ω * W c ω
            * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2 := by
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_range] at hc
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun h' _ => ?_
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [hW']
    rw [if_pos (by omega)]
  have hb : ∑ c ∈ Finset.Ico (κsh' + 1) (κsh + 1), ∑ k ∈ Finset.range K,
      ∑ h' ∈ Finset.Ico (c + e k) (c + e (k + 1)),
        ∑ ω, C.P ω * W' c ω
          * (C.dinc (C.tailSum (c + e (k + 1))) h' ω) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    simp only [Finset.mem_Ico] at hc
    refine Finset.sum_eq_zero fun k _ => ?_
    refine Finset.sum_eq_zero fun h' _ => ?_
    refine Finset.sum_eq_zero fun ω _ => ?_
    simp only [hW']
    rw [if_neg (by omega)]
    ring
  rw [ha, hb, add_zero]

end ChunkSystemB

end KServer


