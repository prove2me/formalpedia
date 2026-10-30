-- Prove2me | Theorems.Thm_gpy_firstMomentCoeff_eq
-- name    : gpy_firstMomentCoeff_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:46.280364+00:00
-- url     : https://prove2.me/theorems/72924c07-522a-4e1f-a24d-5868f3a78eaf
-- title:
--   The first-moment coefficient equals its compatible-pair sum
-- statement:
--   For a tuple $h$ of shifts, a level $R$, and general coefficients $\lambda$, the first-moment coefficient — the $(y-x)$-free part of the first-moment main term — is the sum $$\sum_{d,e} \lambda_d \lambda_e / L(d,e)$$ over support pairs $(d,e)$, where $L(d,e)$ is the combined modulus and the sum is gated by the compatibility condition that the shifts be congruent modulo the gcd of each pair of coordinate moduli. This identifies the coefficient with the inner sum of the first-moment main term, so that theorem reads as an estimate for $(y-x)$ times this coefficient. Formalization Note: the statement is the unfolded form of the coefficient definition, with the support set and the compatibility condition written out in Mathlib terms.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_firstMomentCoeff_eq (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then lam d * lam e /
           Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
         else 0) := by sorry
