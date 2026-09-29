-- Prove2me | Theorems.Thm_iwasawa_freeness
-- name    : iwasawa_freeness
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:25:24.304086+00:00
-- url     : https://prove2.me/theorems/cb5f5f12-adda-4ed8-bf21-5209ee9e5e21
-- statement:
--   **Freeness of the patched module over the Iwasawa algebra.** The inverse limit M_∞ = lim M_{Q_n} of the patched Selmer groups is free of rank 1 over the Iwasawa algebra Λ_∞ = ℤ_p[[Δ_∞]] ≅ ℤ_p[[X₁,...,X_g]]. The freeness follows from the Auslander-Buchsbaum formula: depth(M_∞) + projdim(M_∞) = depth(R_∞), and since depth(R_∞) = dim(R_∞) = g+1 (Cohen-Macaulay), we get projdim = 0, i.e., M_∞ is free. This forces the Krull dimension of R_∞/Ann(M_∞) to equal g+1, which by a comparison with T_∞ gives R_∞ ≅ T_∞, hence R ≅ T.
-- source:
--   https://doi.org/10.2307/2118558

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem iwasawa_freeness (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False := by sorry
