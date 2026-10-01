-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_phi_log_growth_fixed
-- name    : ZudilinZeta.zudilin_phi_log_growth_fixed
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T00:36:06.574307+00:00
-- url     : https://prove2.me/theorems/aa49db0d-ec4b-4d6d-9d7f-80777e662711
-- title:
--   Corrected Chudnovsky–Rukhadze–Hata growth rate of the denominator factor Φₙ
-- statement:
--   CORRECTED Chudnovsky–Rukhadze–Hata analysis of the denominator factor Φₙ. Supersedes ZudilinZeta.zudilin_phi_log_growth (deprecated: FALSE as stated — its claimed limit ∫₀^{1/m_{q−r}} φ(x)/x² dx = 49.5 for params13 is contradicted by the exact computation lim ≈ 176.7506; the integral bounds were inverted). With Φₙ = ∏_{√(η₀n)<p≤m_{q−r}n} p^{φ(n/p)} (product over primes) and φ the 1-periodic integer-valued function of Zudilin's note, the substitution x = n/p sends the prime range to x ≥ 1/m_{q−r}, extending to ∞: lim_{n→∞} (log Φₙ)/n = ∫_{(1/m_{q−r}, ∞)} φ(x)/x² dx (176.75055734 for params13, matching the paper's C₁ = 403 − C₂ with C₂ = 226.24944266). Together with the prime-number-theorem input zudilin_lcm_asymptotics (184bd709-31c9-4dee-9979-715c43c00a36, growth of the D_{m_j n} = lcm(1..m_j n) factors), this yields the constant C₁ — the denominator growth rate in Lemma 3 (ZudilinZeta.zudilin_lemma3) of the mission.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_phi_log_growth_fixed (P : Params) :
    Filter.Tendsto (fun n : ℕ => Real.log (Phi P n : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (∫ x in Set.Ioi (1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2)) := by
  sorry
end ZudilinZeta
