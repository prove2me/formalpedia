-- Prove2me | solution 1 for Mpfx.RoundsFinite.nearest_toEven_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:46.410074+00:00
-- url     : https://prove2.me/submissions/04f49fcb-213a-4d4f-8062-43ca7761dcfc

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_or_eq
section
namespace Mpfx
private theorem dist_eq_of_mem_pair {x : ℝ} {d u y z : Dyadic}
    (hy : y = d ∨ y = u) (hz : z = d ∨ z = u) (hzy : z ≠ y)
    (h : |x - (y : ℝ)| = |x - (z : ℝ)|) : |x - (d : ℝ)| = |x - (u : ℝ)| ∧ d ≠ u := by
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact absurd rfl hzy
  · exact ⟨h, hzy.symm⟩
  · exact ⟨h.symm, hzy⟩
  · exact absurd rfl hzy
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (hy : y = d ∨ y = u) (hclose : |x - (y : ℝ)| ≤ |x - (d : ℝ)| ∧ |x - (y : ℝ)| ≤ |x - (u : ℝ)|)
    (htie : |x - (d : ℝ)| = |x - (u : ℝ)| → d ≠ u →
      F.IsEven y) :
    RoundsFinite F (.nearest .toEven) x y := by
  have hfy : IsFaithfulRound F x y := hy.elim (· ▸ Or.inl hd) (· ▸ Or.inr hu)
  refine ⟨hy.elim (· ▸ hd.1) (· ▸ hu.1), hfy, fun z _ hz => ?_, fun ⟨z, _, hz, hzy, h⟩ => ?_⟩
  · rcases hz.eq_or_eq hd hu with rfl | rfl
    exacts [hclose.1, hclose.2]
  · exact htie (dist_eq_of_mem_pair hy (hz.eq_or_eq hd hu) hzy h).1
      (dist_eq_of_mem_pair hy (hz.eq_or_eq hd hu) hzy h).2
end RoundsFinite
end Mpfx
