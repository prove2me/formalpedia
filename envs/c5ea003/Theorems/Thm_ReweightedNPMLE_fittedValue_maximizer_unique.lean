-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedValue_maximizer_unique
-- name    : ReweightedNPMLE.fittedValue_maximizer_unique
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:31.912948+00:00
-- url     : https://prove2.me/theorems/4db02f8d-4947-5af9-abf1-98bdb57264ce
-- title:
--   Uniqueness of the fitted-value maximizer on a convex feasible set
-- statement:
--   Write $L_w(v)=\sum_iw_i\log v_i$. Let $n\ge1$, let $C\subset(0,\infty)^n$ be convex, and let every $w_i>0$. If $u$ and $v$ both maximize $L_w$ on $C$, then $$u=v.$$ No compactness or existence assumption beyond the two stated maximizers is required. This identifies the unique fitted vector shared by all optimizing mixing laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Weights.lean#L110-L136

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.fittedValue_maximizer_unique {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {u v : Fin n → ℝ}
    (hu : IsMaxOn C (weightedLogLikelihood w) u)
    (hv : IsMaxOn C (weightedLogLikelihood w) v) : u = v := by sorry
