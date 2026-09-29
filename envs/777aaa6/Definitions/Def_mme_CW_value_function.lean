-- Prove2me | Definitions.Def_mme_CW_value_function
-- name    : mme_CW_value_function
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T22:58:54.983018+00:00
-- url     : https://prove2.me/theorems/3a1e0905-9deb-48b5-8c51-f21b7f9078c4
-- statement:
--   **Closed-form Coppersmith–Winograd laser-method value function.**
--
--   For the CW tensor $T_q$ of parameter $q \in \mathbb{N}$, the **asymptotic value** at the trivial spectrum point (the laser-method bound that the τ-theorem consumes) is given explicitly by
--
--   $$\log_2 V(T_q) \;=\; \max_{0 \leq \alpha \leq 1}\; H\!\left(\frac{2-\alpha}{3}, \frac{2\alpha}{3}, \frac{1-\alpha}{3}\right) \;+\; \frac{\alpha}{3} \log_2 q,$$
--
--   where $\alpha \in [0,1]$ is the (symmetric-optimum) probability mass placed on the three "middle" type-triples $\{(0,1,1), (1,0,1), (1,1,0)\}$ of the CW support pattern, and the remaining mass $1-\alpha$ is uniformly distributed on the three "boundary" triples $\{(0,0,2), (0,2,0), (2,0,0)\}$.
--
--   $H(p_1, p_2, p_3) := -p_1 \log_2 p_1 - p_2 \log_2 p_2 - p_3 \log_2 p_3$ is the ternary Shannon entropy in bits.
--
--   **Sources:**
--   - Filmus, *"Limits on the Universal Method for Matrix Multiplication"*, Theorem 2.5 (the cleanest modern formulation): https://www.cs.toronto.edu/~yuvalf/Limitations.pdf
--   - Coppersmith & Winograd 1990 §6 (the original derivation).
--   - Wigderson–Zuiddam tutorial §6 Definition 6.14 (the general `f_p` formalism).
--
--   **Numerical evaluation at $q = 6$**: optimal $\alpha = (-3 + \sqrt{32/q + 1}) / (8/q - 2) = (3 - \sqrt{19/3}) \cdot (3/2) \approx 0.7251$, giving $\log_2 V \approx 1.972$ and $V \approx 3.92$ — comfortably above the threshold $\tfrac{5}{2} = 2.5$ used in our v2 CW chain.
--
--   **Role in the DAG.** This Definition is the **closed-form replacement** for the placeholder `laserValueFormula` (which always returned `1`). It makes `mme_CW_subrank_capacity_poly_lower` and related value-bound theorems provable via numeric computation rather than vacuous against a stub.
--
--   **Reusability.** CW-specific in name but the general `f_p` form generalises to any laser-method tensor; future Stothers/VW/Le Gall papers can reuse this Def's structure (with their own optimization parameter).
-- source:
--   https://www.cs.toronto.edu/~yuvalf/Limitations.pdf

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The closed-form Coppersmith–Winograd laser-method value function

For the Coppersmith–Winograd tensor `T_q` of parameter `q ∈ ℕ`, the **asymptotic
value** at the trivial spectrum point (ρ = 1) is given by the explicit
closed-form formula derived by Coppersmith & Winograd 1990 §6 and stated as
Filmus's "Limits of the Universal Method for Matrix Multiplication"
(Theorem 2.5):

$$\log_2 V(T_q) \;=\; \max_{0 \leq \alpha \leq 1}\;
   H\!\left(\frac{2-\alpha}{3}, \frac{2\alpha}{3}, \frac{1-\alpha}{3}\right)
   \;+\; \frac{\alpha}{3} \log_2 q,$$

where the maximum is over the symmetric-optimum probability mass `α` placed on
the three "middle" type-triples `{(0,1,1), (1,0,1), (1,1,0)}` of the CW
support pattern (with the remaining mass `1-α` placed uniformly on the three
"boundary" triples `{(0,0,2), (0,2,0), (2,0,0)}`).

`H(p_1, p_2, p_3) := -p_1 log_2 p_1 - p_2 log_2 p_2 - p_3 log_2 p_3` is the
ternary Shannon entropy in bits.

**Numerical evaluation at q = 6** (the canonical CW parameter): optimal
`α = (-3 + √(32/6 + 1)) / (8/6 - 2) = (3 - √(19/3)) · (3/2) ≈ 0.7251`, giving
`log₂ V ≈ 1.972` and `V ≈ 3.92` — comfortably above `5/2 = 2.5`.

**Sources:**
- Filmus, "Limits on the Universal Method for Matrix Multiplication", Theorem 2.5.
- Coppersmith & Winograd 1990, §6 (the original laser-method derivation).
- Wigderson–Zuiddam tutorial, §6 Definition 6.14 (general `f_p` formalism).

This file is the **closed-form replacement** for the placeholder
`laserValueFormula` in `Def_mme_laser_pattern`. It only handles the CW case
explicitly — the full general formula (for arbitrary type-graded tensors)
requires the multivariate `f_p` form and is left for follow-up work. -/

universe u

namespace MME

/-- Ternary Shannon entropy in bits. Convention: `0 * log 0 = 0` (Mathlib's
`Real.log 0 = 0` makes this work automatically). -/
noncomputable def H3 (a b c : ℝ) : ℝ :=
  (-a) * (fun x => Real.log x / Real.log 2) a + (-b) * (fun x => Real.log x / Real.log 2) b + (-c) * (fun x => Real.log x / Real.log 2) c

/-- The CW laser-method asymptotic value function at parameter `q`:

$$V(q) \;=\; \sup_{0 \leq \alpha \leq 1}\;
    2^{H((2-\alpha)/3, 2\alpha/3, (1-\alpha)/3) \,+\, (\alpha/3) \log_2 q}.$$

This is the laser-method value of the CW tensor `T_q` at the trivial spectrum
point, via the Coppersmith–Winograd 1990 §6 / Filmus Theorem 2.5 derivation. -/
noncomputable def cwValueFunction (q : ℕ) : ℝ :=
  sSup { v : ℝ | ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
    v = Real.exp (Real.log 2 *
      (H3 ((2 - α) / 3) (2 * α / 3) ((1 - α) / 3)
        + (α / 3) * (fun x => Real.log x / Real.log 2) (q : ℝ))) }

end MME


