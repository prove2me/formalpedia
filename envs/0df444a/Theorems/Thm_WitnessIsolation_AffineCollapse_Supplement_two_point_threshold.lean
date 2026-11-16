-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_two_point_threshold
-- name    : WitnessIsolation.AffineCollapse.Supplement.two_point_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:14.076592+00:00
-- url     : https://prove2.me/theorems/947249fa-db8a-477d-9c5a-a848944aadd3
-- title:
--   Theorem 1.4 — Two-point threshold: success 1/2 + (n+2)^{-c} on two-solution inputs gives NP ⊆ P/poly; one equation gives exactly 1/2
-- statement:
--   Fix $c>0$ and a function $\gamma$ with $\gamma(n)\ge(n+2)^{-c}$ for every $n$.
--
--   1. Suppose a pruning transformation $I$ outputs a uniquely satisfiable circuit with probability at least $1/2+\gamma(n)$ on every input, of any description length, with $n$ variables and exactly two solutions, for all sufficiently large $n$. Then $\mathrm{NP}\subseteq\mathrm{P/poly}$. No guarantee is assumed on inputs with one solution or with more than two.
--   2. Conversely, for every valid description $H$ with $n$ variables, $a\in\mathbb F_2^n$ and $b\in\mathbb F_2$, the one-equation filter is a valid description with
--   $$\mathrm{Sol}\bigl(H\wedge[\langle a,x\rangle=b]\bigr)=\{x\in\mathrm{Sol}(H):\langle a,x\rangle=b\};$$
--   some polynomial pruning family implements $H\mapsto H\wedge[\langle a,x\rangle=b]$ with $a\in\mathbb F_2^n$ and $b\in\mathbb F_2$ uniform; and every such implementation outputs a uniquely satisfiable circuit with probability exactly $1/2$ on every input with one or two solutions, at every $n$ and every description length.
--
--   So $1/2$ is the sharp threshold for two-point inputs, and an inverse-polynomial excess over it already implies small circuits for NP.
--
--   **Formalization Note** The filter is an explicit gate construction (`equationFilter`), and an implementing family reads $a$ and $b$ from fixed tape positions (`ImplementsEquationFilter`). $\mathrm{NP}\subseteq\mathrm{P/poly}$ is the published `NPCollapse`.
--
--   Differences from the source:
--   - encoding: the transformation H ↦ H ∧ [⟨a,x⟩ = b] with a, b uniform → an explicit gate construction with its validity and semantics as a clause, existence of a polynomial pruning family implementing it with a fixed tape layout, and exact success 1/2 for every implementation; reason: this makes the transformation an actual pruning family of the published model; the success clause covers every implementation, including the one asserted to exist
--   - encoding: success on inputs with exactly two solutions "for all sufficiently large n" → TwoPointGuarantee: one threshold n₀ for every description length, plus the published IsPruner; reason: the source quantifies the threshold before the description length
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 3, PDF p. 4, Theorem 1.4; proof pp. 9–10, PDF pp. 10–11 (§4.2)

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_success
import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_filter

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Theorem 1.4 (Two-point threshold), printed p. 3 / PDF p. 4; proof printed pp. 9–10 /
PDF pp. 10–11. (1) Success `1/2 + γ(n)` on two-solution inputs alone, with
`γ(n) ≥ (n+2)^(-c)`, gives NP ⊆ P/poly. (2) The one-equation filter is a correct
syntactic construction, (3) it is realized by a polynomial pruning family, and (4) every
realization succeeds with probability exactly `1/2` on every input with one or two
solutions, at every arity and description length. -/
theorem two_point_threshold :
    (∀ c : ℝ, 0 < c → ∀ γ : ℕ → ℝ,
      (∀ n : ℕ, ((n:ℝ)+2)^(-c) ≤ γ n) →
      ∀ I : PruningFamily, IsPruner I → TwoPointGuarantee I γ → NPCollapse) ∧
    (∀ (d : Description), d.Valid → ∀ (a : Bits d.inputs) (b : Bool),
      (equationFilter d a b).Valid ∧
      ∀ x : Bits d.inputs,
        (equationFilter d a b).eval x = true ↔
          d.eval x = true ∧ dotBit a x = b) ∧
    (∃ I : PruningFamily, IsPruner I ∧ ImplementsEquationFilter I) ∧
    (∀ I : PruningFamily, ImplementsEquationFilter I →
      ∀ L (h : Bits L) (d : Description), decode (List.ofFn h) = some d →
        (d.sol.card = 1 ∨ d.sol.card = 2) →
        uniformProb (fun r : Bits (I.randomLength L) =>
          ∃ e, decode (I.run L h r) = some e ∧ e.sol.card = 1) = 1/2) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
