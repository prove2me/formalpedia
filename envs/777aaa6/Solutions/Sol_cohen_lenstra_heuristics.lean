-- Prove2me | solution 1 for cohen_lenstra_heuristics
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:20.240632+00:00
-- url     : https://prove2.me/submissions/71db79af-abfd-42f5-a82a-672efce6ef6d

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Filter Topology

theorem solution : ¬(∀ (p : ℕ) (hp : Nat.Prime p) (eps : ℝ) (_ : 0 < eps),
    ∃ (C rho : ℝ), 0 < rho ∧ rho < 1 ∧
      (∀ (N : ℕ) (_ : 1 ≤ N),
        |({D : Fin N | ∃ r : ℕ, 1 ≤ r ∧ p ^ r ∣ N}.ncard : ℝ) / N - rho| ≤
        C * (N : ℝ) ^ (-1/2 + eps))) := by
  intro h
  obtain ⟨C, rho, hrho, _, hbound⟩ := h 3 (by decide) (1/4) (by norm_num)
  have hzero (n : ℕ) :
      {D : Fin (3*n+1) | ∃ r : ℕ, 1 ≤ r ∧ 3 ^ r ∣ 3*n+1} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro D ⟨r, hr, hd⟩
    have h3 : 3 ∣ 3*n+1 := (dvd_pow_self 3 (by omega : r ≠ 0)).trans hd
    obtain ⟨q, hq⟩ := h3
    omega
  have hle (n : ℕ) : rho ≤ C * ((3*n+1 : ℕ) : ℝ) ^ (-(1/4 : ℝ)) := by
    have hb := hbound (3*n+1) (by omega)
    rw [hzero, Set.ncard_empty] at hb
    norm_num [abs_of_pos hrho] at hb ⊢
    exact hb
  have htop : Tendsto (fun n : ℕ => ((3*n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 3*n+1) tendsto_id)
  have hlim : Tendsto (fun n : ℕ => C * ((3*n+1 : ℕ) : ℝ) ^ (-(1/4 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp htop))
  exact (not_le_of_gt hrho) (ge_of_tendsto hlim (Eventually.of_forall hle))
