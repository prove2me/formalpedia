-- Prove2me | Theorems.Thm_dalembert_local_min_dichotomy
-- name    : dalembert_local_min_dichotomy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:08:00.580433+00:00
-- url     : https://prove2.me/theorems/23e2d89f-8870-403f-88e2-fa77eb0eda2c
-- statement:
--   **d'Alembert's lemma.** At a local minimum $c$ of $\|f(z)\|$ for a complex polynomial $f$, either $f$ is locally constant near $c$ (i.e. $f(z)=f(c)$ for $z$ near $c$), or $f(c)=0$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
open Polynomial Filter Topology

theorem dalembert_local_min_dichotomy {f : ℂ[X]} {c : ℂ} (hc : IsLocalMin (fun z => ‖f.eval z‖) c) : (∀ᶠ z in 𝓝 c, f.eval z = f.eval c) ∨ f.eval c = 0 := by sorry
