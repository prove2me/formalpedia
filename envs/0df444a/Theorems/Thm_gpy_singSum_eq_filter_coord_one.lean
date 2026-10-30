-- Prove2me | Theorems.Thm_gpy_singSum_eq_filter_coord_one
-- name    : gpy_singSum_eq_filter_coord_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:46.158269+00:00
-- url     : https://prove2.me/theorems/454318bc-f02d-49dc-849c-74a5fa8d21de
-- title:
--   The singular sum sees only the (1,1)-slice at i
-- statement:
--   For a tuple $h$, level $R$, general coefficients $\lambda$, and a coordinate $i$, the singular sum $\mathfrak{S}_i$, the sum of $\lambda_d \lambda_e / \varphi(L(d,e))$ over good support pairs, equals the same sum restricted to support pairs with $d_i = e_i = 1$: every other pair has a false good-indicator, since a good pair at $i$ must have trivial $i$-th coordinates, so its term is $0$. Formalization Note: the singular sum, the support set, and goodness are all written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_singSum_eq_filter_coord_one {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
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
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d => d i = 1),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e => e i = 1),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0) := by sorry
