-- Prove2me | solution 1 for Fpy.rndUnbounded_eq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:53.609262+00:00
-- url     : https://prove2.me/submissions/4909c943-b2aa-4f04-9bfa-0648d0a39536

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_rndInt_congr
import Theorems.Thm_Fpy_p_ne_one_of_top
import Theorems.Thm_Mpfx_canonicalExp_pTop
import Theorems.Thm_Mpfx_isEven_neighbor_iff
import Theorems.Thm_Mpfx_isOdd_neighbor_iff


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F G : FiniteFormat} {rm : RoundingMode}
    (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ} (hGp : G.p = ⊤)
    (hGe : G.exp = ((F.canonicalExp x : ℤ) : QExp)) (hF : ¬ F.IsUndefined rm)
    (hG : ¬ G.IsUndefined rm) : rndUnbounded G rm x hG = rndUnbounded F rm x hF := by
  have he : G.canonicalExp x = F.canonicalExp x := canonicalExp_pTop hGp hGe x
  unfold rndUnbounded
  rw [he]
  congr 1
  refine rndInt_congr rfl Iff.rfl (fun h => ?_) (fun h => ?_)
  · have hG' := isOdd_neighbor_iff (p_ne_one_of_top hGp) (x := x) (by rwa [he])
      (Or.inl (by rw [he]))
    rw [he] at hG'
    rw [hG', isOdd_neighbor_iff hp1 h (Or.inl rfl)]
  · have hG' := isEven_neighbor_iff (p_ne_one_of_top hGp) (x := x) (by rwa [he])
      (Or.inl (by rw [he]))
    rw [he] at hG'
    rw [hG', isEven_neighbor_iff hp1 h (Or.inl rfl)]
end Fpy
