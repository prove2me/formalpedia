-- Prove2me | Theorems.Thm_AbelianTargets_nat_log_scaled_bound
-- name    : AbelianTargets.nat_log_scaled_bound
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:50.459739+00:00
-- url     : https://prove2.me/theorems/fca9b0db-8584-432c-b243-af796a638bf7
-- title:
--   A real-logarithmic bound for the discrete carrier height
-- statement:
--   Let $m,C,L\in\mathbb N$ satisfy $m\ge2$ and $C\ge1$. Write $\log_m^{\mathrm{nat}}R$ for the natural-number logarithm, equal to $\lfloor\log_mR\rfloor$ for positive $R$, and let $\log$ denote the natural logarithm. Define
--   $$
--   \kappa_{m,C}
--   =
--   \frac{1+\log C/\log2}{\log m}+\frac1{\log2}.
--   $$
--   Then
--   $$
--   \log_m^{\mathrm{nat}}\!\bigl(C(L+2)\bigr)+1
--   \le \kappa_{m,C}\log(L+2).
--   $$
--   The estimate includes $L=0$ and converts the discrete height of a finite carrier into a logarithmic rate with an explicit coefficient.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 4 and 6, the logarithmic carrier-height estimate and Proposition 6.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/NaturalLogScaleBounds.lean, authoritative declaration span lines 24-54, SHA-256 e1203dcb79e32a75add81caf96323ab270a5494e173f6154f523bd82f112e0cd. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_NaturalLogScaleBounds
import Init
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-! Converting the literal base-`m` carrier height into the analytic scale bound. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology

theorem AbelianTargets.nat_log_scaled_bound (m : ℕ) (hm : 2≤m) (C : ℕ) (hC : 1≤C) (L : ℕ) :
    (Nat.log m (C*(L+2))+1 : ℝ)≤carrierHeightLogCoefficient m C*Real.log ((L : ℝ)+2) := by sorry
