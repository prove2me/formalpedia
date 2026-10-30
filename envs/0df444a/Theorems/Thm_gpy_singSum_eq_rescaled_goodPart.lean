-- Prove2me | Theorems.Thm_gpy_singSum_eq_rescaled_goodPart
-- name    : gpy_singSum_eq_rescaled_goodPart
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:47.768312+00:00
-- url     : https://prove2.me/theorems/3befa764-1e73-4ff4-bfd9-2187cf1151c0
-- title:
--   The singular sum as a rescaled good part of the first-moment coefficient
-- statement:
--   For a tuple $h$, level $R$, general coefficients $\lambda$, and a coordinate $i$, the singular sum $\mathfrak{S}_i$ is exactly the good-restricted, $(L/\varphi(L))$-rescaled version of the first-moment coefficient's summands: each good pair contributes $(L/\varphi(L)) \cdot \lambda_d \lambda_e / L$, and each non-good pair contributes $0$. No approximation is involved; this is the exact sum-level comparison between the first-moment coefficient and the singular sum. Formalization Note: the singular sum, the support set, goodness, and compatibility are all written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_singSum_eq_rescaled_goodPart {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0)) =
      ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then
          (((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) /
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)) *
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
                h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
             then lam d * lam e /
               Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0)
         else 0) := by sorry
