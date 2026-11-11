-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_succinct_re_complete
-- name    : XORFullTilt.Hardness.succinct_re_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:54:53.222421+00:00
-- url     : https://prove2.me/theorems/a4f96785-c1e4-4924-9549-c66e27016249
-- title:
--   Theorem 4.3 — succinct constant-gap RE-completeness
-- statement:
--   Fix any real $0<\varepsilon<10^{-8}$. The succinct tilted-XOR promise problem has completeness $c=3/4-\varepsilon$ and strict soundness $s=3/4-10^{-8}$. It has a uniform RE separator on finite verifier descriptions and inputs. For every recursively enumerable language $L$ there exist a polynomial-time input map $R$ and a fixed uniform polynomial-time two-prover verifier $V$ with one-bit answers such that
--   $$x\in L\Longrightarrow\omega^*(G_{V,R(x)})\ge\frac34-\varepsilon,$$
--   $$x\notin L\Longrightarrow\omega^*(G_{V,R(x)})<\frac34-10^{-8}.$$
--   The verifier uses a polynomial-length random tape and questions. All polynomial bounds are uniform in the input and may depend on $L$ and the fixed threshold parameter. Expanding its finite game table is computable, with no polynomial expansion claim. This is the full succinct theorem used to obtain the explicit version.
--
--   Differences from the source:
--   - encoding: polynomial-time probabilistic verifiers with polynomial-length questions → finite charged program syntax with polynomial runtime, tape and question bounds, padded bit questions and a separately tagged distinguished question; reason: size-faithful encodings and bounded fair-bit sampling realize the same uniform polynomial-time verifier model; fixed program descriptions and a polynomial-time input map specify the reduction
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.20, Theorem 4.3 and explicit-constant paragraph

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_EffectiveGames

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Theorem 4.3 with the explicit thresholds from p.20, for every allowed ε.
    A fixed uniform verifier and a polynomial-time input map describe the reduction. -/
theorem succinct_re_complete (ε : ℝ) (hε : 0 < ε) (hsmall : ε < (1/100000000 : ℝ)) :
    SuccinctPromiseRE ((3/4 : ℝ)-ε) ((3/4 : ℝ)-(1/100000000 : ℝ)) ∧
    (∀ L : List Bool → Prop, REPred L →
      ∃ R : MIPRE.Cost.PolyTimeFun (List Bool) (List Bool), ∃ V : SuccinctVerifier,
        (∀ x, L x → succinctValue V (R x) ≥ (3/4 : ℝ)-ε) ∧
        (∀ x, ¬ L x → succinctValue V (R x) < (3/4 : ℝ)-(1/100000000 : ℝ))) := by sorry

end XORFullTilt.Hardness
