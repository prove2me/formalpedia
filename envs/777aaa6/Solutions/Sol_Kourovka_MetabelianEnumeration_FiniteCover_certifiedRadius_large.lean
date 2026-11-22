-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.certifiedRadius_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:22.724176+00:00
-- url     : https://prove2.me/submissions/cc63831c-acee-4361-8bf8-4de7133c7951

import Definitions.Def_Kourovka_Polyhedral_Radius
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Covers_CertifiedRadius

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {C D : ℚ}
    (hC : 0 < C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    2 * (k : ℚ) < certifiedRadius k C D ∧
    2 * (k : ℚ) * D < certifiedRadius k C D ∧
    C < certifiedRadius k C D ∧
    D ^ 2 < C * certifiedRadius k C D := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hquot : 0 ≤ D ^ 2 / C := div_nonneg (sq_nonneg D) (le_of_lt hC)
  have hceil := Nat.le_ceil (2 * (k : ℚ) * (1 + D + D ^ 2 / C))
  have hmain : 2 * (k : ℚ) * (1 + D + D ^ 2 / C) < certifiedRadius k C D := by
    simp only [certifiedRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hbase : 0 < 2 * (k : ℚ) * (1 + D + D ^ 2 / C) := by positivity
  have hfirst : 2 * (k : ℚ) < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℚ) by linarith) hquot]
  have hsecond : 2 * (k : ℚ) * D < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℚ) by linarith) hquot]
  have hthird : C < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℚ) - 1 by linarith)
      (show 0 ≤ D by linarith)]
  have hfourth : D ^ 2 / C < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℚ) - 1 by linarith) hquot,
      mul_nonneg (show 0 ≤ (k : ℚ) by linarith) (show 0 ≤ D by linarith)]
  exact ⟨hfirst, hsecond, hthird, by
    have := (div_lt_iff₀ hC).mp hfourth
    nlinarith⟩
end Kourovka.MetabelianEnumeration.FiniteCover
