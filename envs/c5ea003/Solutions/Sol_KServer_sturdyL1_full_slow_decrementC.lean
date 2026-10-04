-- Prove2me | solution 1 for KServer.sturdyL1_full_slow_decrementC
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T22:31:52.178433+00:00
-- url     : https://prove2.me/submissions/cb5e1505-2800-4772-bfc2-4f7c781ca90f

import Mathlib
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_chunk_slow_decrement_cond
import Definitions.Def_KServer_chunk_stopping

open KServer ChunkSystemB

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ} (hcHi : 0 ≤ cHi)
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (hst : C.SturdyL1 C.m 0) :
    C.SlowDecrementC cHi := by
  -- Step 1a.  Zero defect bounds the sum of the nonnegative summands
  -- `P ω * max (expTotal - doobTotal n ω) 0` by `0`, so the sum vanishes
  -- and therefore every summand does.
  have hall : ∀ (n : ℕ) (hn : n ≤ C.m) (ω : C.Ω),
      C.P ω * max (C.expTotal - C.doobTotal n ω) 0 = 0 := by
    intro n hn ω
    have hzero : (∑ ω' : C.Ω, C.P ω' * max (C.expTotal - C.condExp C.totalSize n ω') 0) = 0 :=
      le_antisymm (hst n hn)
        (Finset.sum_nonneg fun ω' _ =>
          mul_nonneg (le_of_lt (C.hP ω')) (le_max_right _ _))
    have hsingle := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset C.Ω))
      (f := fun ω' => C.P ω' * max (C.expTotal - C.condExp C.totalSize n ω') 0)
      (fun ω' _ => mul_nonneg (le_of_lt (C.hP ω')) (le_max_right _ _))).mp hzero
    have hone : C.P ω * max (C.expTotal - C.doobTotal n ω) 0 = 0 := by
      simpa only [ChunkSystemB.doobTotal] using hsingle ω (Finset.mem_univ ω)
    exact hone
  -- The second factor vanishes, because `P ω` is strictly positive.
  have hmax0 : ∀ (n : ℕ) (hn : n ≤ C.m) (ω : C.Ω),
      max (C.expTotal - C.doobTotal n ω) 0 = 0 := by
    intro n hn ω
    rcases mul_eq_zero.mp (hall n hn ω) with hzero' | hzero'
    · exact absurd hzero' (ne_of_gt (C.hP ω))
    · exact hzero'
  -- Step 1b.  Hence `doobTotal n ω ≥ expTotal` pointwise for `n ≤ C.m`.
  have hge : ∀ (n : ℕ) (hn : n ≤ C.m) (ω : C.Ω), C.expTotal ≤ C.doobTotal n ω := by
    intro n hn ω
    exact sub_nonpos.mp ((le_max_left _ _).trans (hmax0 n hn ω).le)
  -- Step 1c.  The tower identity `sum_mul_condExp` says the weighted sum of
  -- `doobTotal n` is exactly `expTotal`; the pointwise bound makes every
  -- deviation nonnegative, so every deviation vanishes.
  have hflat : ∀ (n : ℕ) (hn : n ≤ C.m) (ω : C.Ω), C.doobTotal n ω = C.expTotal := by
    intro n hn ω
    have h1 := C.sum_mul_condExp C.totalSize n
    have h3 : (∑ ω' : C.Ω, C.P ω' * C.doobTotal n ω') = C.expTotal := by
      calc (∑ ω' : C.Ω, C.P ω' * C.doobTotal n ω')
          = ∑ ω' : C.Ω, C.P ω' * C.totalSize ω' := by
            simp only [ChunkSystemB.doobTotal]
            exact h1
        _ = C.expTotal := rfl
    have hexp : (∑ ω' : C.Ω, C.P ω' * C.expTotal) = C.expTotal := by
      calc (∑ ω' : C.Ω, C.P ω' * C.expTotal)
          = (∑ ω' : C.Ω, C.P ω') * C.expTotal := (Finset.sum_mul _ _ _).symm
        _ = 1 * C.expTotal := by rw [C.hPsum]
        _ = C.expTotal := one_mul _
    have hdev : (∑ ω' : C.Ω, C.P ω' * (C.doobTotal n ω' - C.expTotal)) = 0 := by
      have hsp : (∑ ω' : C.Ω, C.P ω' * C.doobTotal n ω')
              - ∑ ω' : C.Ω, C.P ω' * C.expTotal = 0 := by rw [h3, hexp]; ring
      have hd := Finset.sum_sub_distrib (s := (Finset.univ : Finset C.Ω))
        (fun ω' => C.P ω' * C.doobTotal n ω') (fun ω' => C.P ω' * C.expTotal)
      calc (∑ ω' : C.Ω, C.P ω' * (C.doobTotal n ω' - C.expTotal))
          = (∑ ω' : C.Ω, (C.P ω' * C.doobTotal n ω' - C.P ω' * C.expTotal)) := by
              congr 1; funext ω'; ring
        _ = (∑ ω' : C.Ω, C.P ω' * C.doobTotal n ω')
              - ∑ ω' : C.Ω, C.P ω' * C.expTotal := hd
        _ = 0 := hsp
    have hall' := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset C.Ω))
      (f := fun ω' => C.P ω' * (C.doobTotal n ω' - C.expTotal))
      (fun ω' _ =>
        mul_nonneg (le_of_lt (C.hP ω')) (sub_nonneg.mpr (hge n hn ω')))).mp hdev
    have hprod : C.P ω * (C.doobTotal n ω - C.expTotal) = 0 :=
      hall' ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp hprod with hzero' | hzero'
    · exact absurd hzero' (ne_of_gt (C.hP ω))
    · exact sub_eq_zero.mp hzero'
  -- Step 2.  `doobTotal = pastSize + condFuture` turns (1c) into a closed form
  -- for the conditional expected remaining size.
  have hsplit : ∀ (n : ℕ) (hn : n ≤ C.m) (ω : C.Ω),
      C.condFuture n ω = C.expTotal - C.pastSize n ω := by
    intro n hn ω
    have h1 := C.doobTotal_eq_past_add_condFuture n ω
    have h2 := hflat n hn ω
    linarith
  -- Step 3.  Consecutive `condFuture` values differ by the `h`-th chunk size,
  -- which is bounded by `cHi`; for `h ≥ C.m` both sides vanish.
  have hdrop : ∀ (h : ℕ) (ω : C.Ω), C.condFuture h ω - cHi ≤ C.condFuture (h + 1) ω := by
    intro h ω
    by_cases hm : C.m ≤ h
    · have hz1 := C.condFuture_of_m_le hm ω
      have hz2 := C.condFuture_of_m_le (Nat.le_trans hm (Nat.le_succ h)) ω
      linarith
    · have hlt : h < C.m := Nat.lt_of_not_ge hm
      have h1 := hsplit h hlt.le ω
      have h2 := hsplit (h + 1) (by omega) ω
      have h3 := C.pastSize_succ h ω
      have h4 := C.sizeN_le hlt ω
      linarith
  intro h ω
  exact hdrop h ω
