-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_correction_sum_le
-- name    : ZeroFreeBridge.norm_correction_sum_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:20.860726+00:00
-- url     : https://prove2.me/theorems/cfe304d9-71de-4364-83a2-6b43c73029b0
-- title:
--   Bound for the canonical-factor correction
-- statement:
--   Let $R>0$, $S\subset B(0,R)$ be finite, $n:S\to\mathbb Z$, and $|z|<R$. Then
--   $$\left|\sum_{u\in S}\frac{n(u)\overline u}{R^2-\overline u z}\right|
--   \le\frac{\sum_{u\in S}|n(u)|}{R-|z|}.$$
--   This controls the correction in the logarithmic-derivative decomposition.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpCorrectionBound.lean#L19-L54

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE item (d3)): the Blaschke correction sum is O(L).

   Expanding `DlvpBlaschkeSplit.logDeriv_split_off_zeros` via `DlvpCanonicalLogDeriv.logDeriv_
   canonicalFactor`, each term splits into the monomial Herglotz contribution and a CORRECTION
   `(n u)·conj u/(R² − conj u·z)`.  The correction is bounded because its pole `R²/conj u` lies
   OUTSIDE the disk: `|R² − conj u·z| ≥ R² − ‖u‖‖z‖ ≥ R(R − ‖z‖) > 0`, so per term

     `‖(n u)·conj u/(R² − conj u·z)‖ ≤ |n u|/(R − ‖z‖)` ,

   and summing gives `‖Σ correction‖ ≤ (Σ |n u|)/(R − ‖z‖)` — a constant `O(1)` times the zero count
   `Σ|n u| = O(L)`.  Function-agnostic in `n`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_correction_sum_le {R : ℝ} (hR : 0 < R) (n : ℂ → ℤ) (s : Finset ℂ)
    (hsupp : ∀ u ∈ s, u ∈ ball (0 : ℂ) R) {z : ℂ} (hz : ‖z‖ < R) :
    ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ (∑ u ∈ s, |(n u : ℝ)|) / (R - ‖z‖) := by sorry
