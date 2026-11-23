-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bethe_canonical_local
-- name    : ZeroFreeRRG.Hardcore.bethe_canonical_local
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:24:29.210926+00:00
-- url     : https://prove2.me/theorems/4a283b33-3cd6-400a-b030-19d6f8640460
-- title:
--   Local Bethe canonical form on simple configuration-model graphs
-- statement:
--   Fix $d\ge3$ and a nontrivial parameter $t$ for the hardcore model or the $q$-state antiferromagnetic Potts model ($q\ge2$). On a sufficiently small closed complex disk about $t$ there is a nowhere-zero function $C(z)$ such that, for every simple pairing on $n$ vertices with contracted graph $G$,
--   $$
--   Z_G(z)=C(z)^n\,\mathcal Z_G(z)
--   $$
--   throughout that disk. Here $Z_G$ is the hardcore independence polynomial in the $\alpha$-parametrization or the Potts partition function, and $\mathcal Z_G$ is the normalized partition function.
--
--   This is the explicit Bethe canonical form of Definition 2.5. For hardcore one may take $C_d(\alpha)=(1-\alpha)^{d-1}(1-2\alpha)^{-d/2}$; for Potts, $C_{d,q}(\beta)=q((q-1+\beta)/q)^{d/2}$. The disk is shrunk to avoid zeros of the denominators.
--
--   **Formalization Note.** Natural-number division gives the exponent $d/2$, so the two displayed formulas are interpreted with matching integer powers in the proof.
-- source:
--   Chen, Wang, Zhang, arXiv:2610.40510, p. 16, equations (6)–(7) and Definition 2.5, equation (8); applied to simple CM graphs in the proof of Theorem 5.1, p. 40.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel

open scoped Classical
open AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- On a sufficiently small disk about a nontrivial real parameter there is a nonvanishing factor `C`
such that the unnormalized partition function of a simple contracted pairing is the Bethe canonical
form `(C z)^n * normZ`. -/
theorem bethe_canonical_local (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℂ → ℂ,
      (∀ z ∈ Metric.closedBall (t : ℂ) R, C z ≠ 0) ∧
      ∀ n : ℕ, ∀ M : Matching n d, IsSimpleM M →
        ∀ z ∈ Metric.closedBall (t : ℂ) R,
          m.Zgraph d (toGraph M) z = (C z) ^ n * normZ m z M := by sorry
