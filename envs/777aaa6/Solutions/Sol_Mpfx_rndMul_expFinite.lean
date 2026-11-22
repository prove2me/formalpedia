-- Prove2me | solution 1 for Mpfx.rndMul_expFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:37.337257+00:00
-- url     : https://prove2.me/submissions/f5ba8d17-3112-48da-a046-75009f521744

import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_Mul
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mul
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_mul
import Theorems.Thm_Mpfx_Format_mem_unbounded_of_le
import Theorems.Thm_Mpfx_rndExact

section
namespace Mpfx
private theorem mul_mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂) (he : F₂.exp ≤ F₁.exp + F₁.exp)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) :
    (x * y : Dyadic) ∈ F₂.unbounded :=
  -- the product lives in the intermediate format `𝒜(2p₁, exp₁+exp₁, ⊤)`, which
  -- is contained in `F₂.unbounded` by `𝒜-Contains-Prec` (`mem_unbounded_of_le`).
  Format.mem_unbounded_of_le (p := ((2 * p₁ : ℕ) : Prec))
    (by rw [hp₂]; exact ENat.coe_le_coe.mpr hpp) he
    (by rw [two_mul, Nat.cast_add]; exact Dyadic.precisionAtMost_mul (hp₁ ▸ hx.1) (hp₁ ▸ hy.1))
    (Dyadic.quantumAtLeast_mul hx.2.1 hy.2.1)
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ 2 * emin₁)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndExact (mul_mem_F₂_unbounded hp₁ hp₂ hpp
    (by rw [hexp₁, hexp₂, ← WithBot.coe_add]; exact_mod_cast (by omega : emin₂ ≤ emin₁ + emin₁))
    hx hy) hz hw
end Mpfx
