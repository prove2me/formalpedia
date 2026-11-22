-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.dyadic_margin_search_terminates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:36.72728+00:00
-- url     : https://prove2.me/submissions/609505d5-bf02-415f-ad02-a0e1c2d91259

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_exists_uniform_margin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_checkMargin_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n)
    (hc : ConeCover supports) : ∃ r : ℕ, checkMargin supports ((1 / 2 : ℚ) ^ r) = true := by
  obtain ⟨epsilon, he0, _, hmargin⟩ := exists_uniform_margin supports hc
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one he0 (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨r, (checkMargin_correct supports _).mpr ?_⟩
  intro x hx
  obtain ⟨s, hs, hpos⟩ := hmargin x hx
  refine ⟨s, hs, ?_⟩
  intro u hu
  have hcast : (((1 / 2 : ℚ) ^ r : ℚ) : ℝ) < epsilon := by
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hr
  exact hcast.trans (hpos u hu)
end Kourovka.MetabelianEnumeration.ConeVerifier
