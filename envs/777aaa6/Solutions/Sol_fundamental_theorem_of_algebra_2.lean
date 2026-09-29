-- Prove2me | solution 2 for fundamental_theorem_of_algebra
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:35:08.689431+00:00
-- url     : https://prove2.me/submissions/49fceca7-c6e8-42e6-aa65-8746ea92dc91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_fundamental_theorem_of_algebra
import Theorems.Thm_polynomial_eval_norm_tendsto_cobounded
import Theorems.Thm_liouville_eq_const_of_tendsto_cocompact
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Sketch — Fundamental Theorem of Algebra via Liouville (the Mathlib proof)

Mirrors Mathlib's own `Complex.exists_root`: a decomposition of the parent
`fundamental_theorem_of_algebra` distinct from the minimum-modulus route.

```
fundamental_theorem_of_algebra                  (target)
  ├── polynomial_eval_norm_tendsto_cobounded     (Child 1 — ‖f.eval z‖ → ∞ at ∞)
  └── liouville_eq_const_of_tendsto_cocompact    (Child 2 — Liouville, limit form)
```

Argument: if `f` has no root then `z ↦ (f.eval z)⁻¹` is entire (Child-free:
`f` differentiable + never zero). By Child 1 `‖f.eval z‖ → ∞`, so `(f.eval z)⁻¹
→ 0` at infinity; by Child 2 (Liouville) it is identically `0`, forcing `f`
constant — contradicting `0 < degree f`.

This sketch is `sorry`-free; the two children carry the `sorry`s.
-/

open Polynomial Filter Topology

theorem solution (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ z : ℂ, f.IsRoot z := by
  by_contra! hf'
  -- `f` never vanishes, so `1 / f` is entire.
  have hdiff : Differentiable ℂ (fun z => (f.eval z)⁻¹) := f.differentiable.inv hf'
  -- Child 1: `‖f.eval z‖ → ∞` at infinity.
  have hgrow : Tendsto (fun z : ℂ => ‖f.eval z‖) (Bornology.cobounded ℂ) atTop :=
    polynomial_eval_norm_tendsto_cobounded hf
  -- Hence `f.eval` escapes every bounded set along `cocompact`.
  have heval : Tendsto (fun z : ℂ => f.eval z) (cocompact ℂ) (Bornology.cobounded ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact hgrow
  -- So `(f.eval z)⁻¹ → 0` at infinity.
  have hinv : Tendsto (fun z : ℂ => (f.eval z)⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp heval
  -- Child 2 (Liouville): an entire function tending to `0` at infinity is `0`.
  have hzero : ∀ z : ℂ, (f.eval z)⁻¹ = 0 := fun z =>
    liouville_eq_const_of_tendsto_cocompact hdiff hinv z
  -- Inverting, `f` is the constant polynomial `0` — impossible for positive degree.
  obtain rfl : f = C 0 := Polynomial.funext fun z => inv_injective (by simp [hzero])
  simp at hf
