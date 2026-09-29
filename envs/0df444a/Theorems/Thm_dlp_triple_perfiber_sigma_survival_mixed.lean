-- Prove2me | Theorems.Thm_dlp_triple_perfiber_sigma_survival_mixed
-- name    : dlp_triple_perfiber_sigma_survival_mixed
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-24T03:08:38.761266+00:00
-- url     : https://prove2.me/theorems/f20a99d4-3844-499a-985c-0041e612de75
-- statement:
--   Order-3 hypothesis-free per-fiber sigma-survival lower bound on the concrete matrix MIXED (linear + bilinear + trilinear, degree-<=3) sign-chaos: for ANY coefficient families b, a, cc and any matrix T, the Rademacher-sigma survival probability P_sigma(spectralNorm T <= spectralNorm (T + Xi)) >= 1/2916, where Xi(eps) = sum_w sgn_w . b_w + sum_{w1!=w2} sgn.sgn . a + sum_{w1,w2,w3 distinct} sgn.sgn.sgn . cc. Order-3 analog of dlp_pair_perfiber_sigma_survival_mixed (db8a020b). Composes spectral-norm dual attainment (norming pair), mean-zero of the dual-image chaos (linear/bilinear/trilinear via the single/pair/triple-coordinate Bernoulli marginals), and a case split on the sigma-variance: positive variance routes through the order-3 mixed conditional Lemma 2 (1/2916=1/(4*729)); degenerate variance gives a constant-1 survival indicator. Source: de la Pena-Montgomery-Smith 1995 (arXiv:math/9309211) sec 4 eq (6) / Lemma 2; the trilinear mean-zero uses coordinate independence of the symmetric Bernoulli (p=1/2) measure.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_triple_perfiber_sigma_survival_mixed
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (cc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                        * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  sorry
