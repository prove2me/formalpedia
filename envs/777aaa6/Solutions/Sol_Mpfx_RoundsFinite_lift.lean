-- Prove2me | solution 1 for Mpfx.RoundsFinite.lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:35:36.778929+00:00
-- url     : https://prove2.me/submissions/514c74b8-6de1-46e7-83c5-d1c63e3df6a5

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Restrict
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_or_eq
import Theorems.Thm_Mpfx_IsFaithfulRound_of_subset
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil
import Theorems.Thm_Mpfx_boundOK_of_between
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem

section
namespace Mpfx
private theorem RoundsFinite.toNegative_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toNegative x w)
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toNegative x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, fun v hv hvx =>
    (hy.2.2 v hv hvx).trans (hw.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1)⟩
private theorem RoundsFinite.toPositive_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toPositive x w)
    (hy : RoundsFinite F.unbounded .toPositive x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toPositive x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, fun v hv hxv =>
    (hw.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1).trans (hy.2.2 v hv hxv)⟩
private theorem RoundsFinite.toZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toZero x w)
    (hy : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toZero x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, hw.2.2.1, fun v hv hvb hvs => (hy.2.2.2 v hv hvb hvs).trans
    (hw.2.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1 hy.2.2.1)⟩
private theorem RoundsFinite.awayZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .awayZero x w)
    (hy : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .awayZero x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, hw.2.2.1, fun v hv hvb hvs =>
    (hw.2.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1 hy.2.2.1).trans
      (hy.2.2.2 v hv hvb hvs)⟩
private theorem IsFaithfulRound.restrict {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F x y :=
  h.of_subset F.subset_unbounded
    (mem_of_mem_unbounded_of_boundOK (h.elim (·.1) (·.1)) hb)
private theorem IsFaithfulRound.unbounded_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : IsFaithfulRound F x w)
    (hy : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F.unbounded x w := by
  have hd := RoundsFinite.toNegative_floor F x
  have hu := RoundsFinite.toPositive_ceil F x
  have hwF : w ∈ F := hw.elim (·.1) (·.1)
  rcases hw with hw | hw
  · refine Or.inl (RoundsFinite.toNegative_lift hw hd ?_)
    rcases hy.eq_or_eq hd hu with rfl | rfl
    · exact hb
    · exact boundOK_of_between hwF.2.2 hb (hd.2.2 w (mem_unbounded_of_mem hwF) hw.2.1)
        (hd.2.1.trans hu.2.1)
  · refine Or.inr (RoundsFinite.toPositive_lift hw hu ?_)
    rcases hy.eq_or_eq hd hu with rfl | rfl
    · exact boundOK_of_between hb hwF.2.2 (hd.2.1.trans hu.2.1)
        (hu.2.2 w (mem_unbounded_of_mem hwF) hw.2.1)
    · exact hb
private theorem RoundsFinite.toOdd_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toOdd x w)
    (hy : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toOdd x w := by
  obtain ⟨hwmem, hwfaithful, hwparity⟩ := hw
  exact ⟨mem_unbounded_of_mem hwmem,
    IsFaithfulRound.unbounded_lift hwfaithful hy.2.1 hb,
    hwparity⟩
private theorem faithful_eq_of_third {F : FiniteFormat} {x : ℝ} {w y c : Dyadic}
    (hwf : IsFaithfulRound F.unbounded x w)
    (hyf : IsFaithfulRound F.unbounded x y)
    (hcf : IsFaithfulRound F.unbounded x c)
    (hc_ne_w : c ≠ w) (hc_ne_y : c ≠ y) : y = w := by
  have hd := RoundsFinite.toNegative_floor F x
  have hu := RoundsFinite.toPositive_ceil F x
  rcases hwf.eq_or_eq hd hu with hw | hw <;> rcases hyf.eq_or_eq hd hu with hy | hy <;>
    rcases hcf.eq_or_eq hd hu with hc | hc <;>
    first
    | exact hy.trans hw.symm
    | exact absurd (hc.trans hw.symm) hc_ne_w
    | exact absurd (hc.trans hy.symm) hc_ne_y
private theorem RoundsFinite.nearest_lift {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {w y : Dyadic} (hw : RoundsFinite F (.nearest tb) x w)
    (hy : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded (.nearest tb) x w := by
  cases tb with
  | toEven =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · rintro ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
      by_cases hcb : Format.boundOK F.b c
      · exact hwtie ⟨c, mem_of_mem_unbounded_of_boundOK hc hcb,
          IsFaithfulRound.restrict hc_faithful hcb, hc_ne, hc_tie⟩
      · -- `c` out of bound forces `y = w`; fire `y`'s own tie clause.
        have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
  | awayZero =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · intro c hc hc_faithful hc_ne hc_tie
      by_cases hcb : Format.boundOK F.b c
      · exact hwtie c (mem_of_mem_unbounded_of_boundOK hc hcb)
          (IsFaithfulRound.restrict hc_faithful hcb) hc_ne hc_tie
      · have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie c hc hc_faithful hc_ne hc_tie
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F rm x w)
    (hy : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded rm x w := by
  cases rm with
  | toNegative => exact toNegative_lift hw hy hb
  | toPositive => exact toPositive_lift hw hy hb
  | toZero => exact toZero_lift hw hy hb
  | awayZero => exact awayZero_lift hw hy hb
  | toOdd => exact toOdd_lift hw hy hb
  | nearest _ => exact nearest_lift hw hy hb
end RoundsFinite
end Mpfx
