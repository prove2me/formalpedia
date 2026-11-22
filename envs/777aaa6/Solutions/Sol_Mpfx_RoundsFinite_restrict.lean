-- Prove2me | solution 1 for Mpfx.RoundsFinite.restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:35:36.270554+00:00
-- url     : https://prove2.me/submissions/4e168c22-f7a7-44f5-b56b-7899080c5349

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Restrict
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_IsFaithfulRound_of_subset
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem

section
namespace Mpfx
private theorem IsFaithfulRound.restrict {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F x y :=
  h.of_subset F.subset_unbounded
    (mem_of_mem_unbounded_of_boundOK (h.elim (·.1) (·.1)) hb)
private theorem nearest_close_upgrade {F : FiniteFormat} {x : ℝ} {y c : Dyadic}
    (hy_close : ∀ v : Dyadic, v ∈ F.unbounded → IsFaithfulRound F.unbounded x v →
      |x - (y : ℝ)| ≤ |x - (v : ℝ)|)
    (hc : c ∈ F) (hc_faithful : IsFaithfulRound F x c) :
    |x - (y : ℝ)| ≤ |x - (c : ℝ)| ∧
      (|x - (y : ℝ)| = |x - (c : ℝ)| → IsFaithfulRound F.unbounded x c) := by
  -- The unbounded neighbour `g` on `c`'s side lies between `c` and `x`.
  obtain ⟨g, hg, hgc, hgc_eq⟩ : ∃ g : Dyadic, IsFaithfulRound F.unbounded x g ∧
      |x - (g : ℝ)| ≤ |x - (c : ℝ)| ∧ (|x - (g : ℝ)| = |x - (c : ℝ)| → g = c) := by
    rcases hc_faithful with ⟨-, hcx, -⟩ | ⟨-, hxc, -⟩
    · have hd := RoundsFinite.toNegative_floor F x
      have hcd := hd.2.2 c (mem_unbounded_of_mem hc) hcx
      have e₁ := abs_of_nonneg (sub_nonneg.mpr hd.2.1)
      have e₂ := abs_of_nonneg (sub_nonneg.mpr hcx)
      exact ⟨_, Or.inl hd, by rw [e₁, e₂]; linarith,
        fun h => Dyadic.ext_real (by rw [e₁, e₂] at h; linarith)⟩
    · have hu := RoundsFinite.toPositive_ceil F x
      have huc := hu.2.2 c (mem_unbounded_of_mem hc) hxc
      have e₁ := abs_of_nonpos (sub_nonpos.mpr hu.2.1)
      have e₂ := abs_of_nonpos (sub_nonpos.mpr hxc)
      exact ⟨_, Or.inr hu, by rw [e₁, e₂]; linarith,
        fun h => Dyadic.ext_real (by rw [e₁, e₂] at h; linarith)⟩
  have h₁ := hy_close g (hg.elim (·.1) (·.1)) hg
  exact ⟨h₁.trans hgc, fun h => hgc_eq (le_antisymm hgc (h.symm.le.trans h₁)) ▸ hg⟩
private theorem RoundsFinite.nearest_restrict {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {y : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F (.nearest tb) x y := by
  cases tb with
  | toEven =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · rintro ⟨c, hcF, hc_faithful, hc_ne, hc_tie⟩
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact htie ⟨c, mem_unbounded_of_mem hcF, hc_up, hc_ne, hc_tie⟩
  | awayZero =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · intro c hcF hc_faithful hc_ne hc_tie
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact htie c (mem_unbounded_of_mem hcF) hc_up hc_ne hc_tie
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F rm x y := by
  have hm := mem_of_mem_unbounded_of_boundOK h.1 hb
  cases rm with
  | toNegative | toPositive => exact ⟨hm, h.2.1, fun v hv => h.2.2 v (mem_unbounded_of_mem hv)⟩
  | toZero | awayZero =>
    exact ⟨hm, h.2.1, h.2.2.1, fun v hv => h.2.2.2 v (mem_unbounded_of_mem hv)⟩
  | toOdd => exact ⟨hm, IsFaithfulRound.restrict h.2.1 hb, h.2.2⟩
  | nearest _ => exact nearest_restrict h hb
end RoundsFinite
end Mpfx
