-- Prove2me | Definitions.Def_mme_auto_scaled_log_interval_data
-- name    : mme_auto_scaled_log_interval_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T14:58:06.483252+00:00
-- url     : https://prove2.me/theorems/888a878e-c4c5-4260-b651-7647f1df8369
-- title:
--   Computed endpoints of an auto-scaled rational logarithm interval
-- statement:
--   Computed endpoints for a rigorous logarithm interval of a positive rational.
--
--   For a rational $q$ and a scale $k$, utoScaledLogParameter is the atanh parameter $t = (q 2^k - 1)/(q 2^k + 1)$, utoScaledLogPartial is the truncated series $\sum_{i<n} t^{2i+1}/(2i+1)$, and the two endpoints are
--
--   $$L = 2 S_n - k \cdot 0.69314718057, \qquad U = 2\Big(S_n + \frac{t^{2n+1}}{1-t^2}\Big) - k \cdot 0.69314718055 .$$
--
--   The two decimal constants bracket $\log 2$, so subtracting $k$ of them undoes the scaling in the safe direction on each side. Everything here is exact rational arithmetic: a table of logarithms need store only $q$ and $k$, and its interval endpoints are then computed rather than assumed.
-- source:
--   Support data for the exact rational logarithm certificates used by the scalar bookkeeping of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5.

import Mathlib.Tactic

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

namespace MME

/-- The atanh parameter after scaling a positive rational into the interval
starting at one. -/
def autoScaledLogParameter (q : ℚ) (k : ℕ) : ℚ :=
  (q * 2 ^ k - 1) / (q * 2 ^ k + 1)

def autoScaledLogPartial (q : ℚ) (k n : ℕ) : ℚ :=
  ∑ i ∈ range n,
    autoScaledLogParameter q k ^ (2 * i + 1) / (2 * i + 1)

def autoScaledLogLower (q : ℚ) (k n : ℕ) : ℚ :=
  2 * autoScaledLogPartial q k n -
    k * (69314718057 / 100000000000 : ℚ)

def autoScaledLogUpper (q : ℚ) (k n : ℕ) : ℚ :=
  2 * (autoScaledLogPartial q k n +
    autoScaledLogParameter q k ^ (2 * n + 1) /
      (1 - autoScaledLogParameter q k ^ 2)) -
    k * (69314718055 / 100000000000 : ℚ)

end MME


