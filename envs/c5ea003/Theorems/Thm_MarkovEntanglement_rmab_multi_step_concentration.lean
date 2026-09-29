-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_multi_step_concentration
-- name    : MarkovEntanglement.rmab_multi_step_concentration
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:23:35.584299+00:00
-- url     : https://prove2.me/theorems/8e28ce63-c269-476f-b31e-74ace8434a01
-- title:
--   Multi-step concentration of the configuration (Lem. 10, Gast et al. 2023)
-- statement:
--   There is a constant $K$, independent of the system size $N$, such that for every horizon $t$ and every $\delta > 0$ the configuration of the $N$-agent chain after $t$ steps stays close to the $t$-th iterate of the explicit mean-field map applied to the starting configuration:
--
--   $$\Pr\Big[\, \|m[t] - \Phi^t(m)\|_\infty \ge (1 + K + K^2 + \cdots + K^t)\,\delta \;\Big|\; m[0] = m \,\Big] \;\le\; 2\,t\,|S|\,e^{-N\delta^2/2},$$
--
--   where $\Phi$ is the explicit mean-field map at the system's exact activation fraction $\lfloor \alpha N \rfloor / N$. The iterate must be that of the explicit map: a map merely characterised on the configurations the $N$-agent system can occupy leaves that lattice after one step, and off the lattice the characterisation says nothing, so no bound of this shape could hold for it.
--
--   Two effects are being combined. Each single step contributes a deviation of size $\delta$ with failure probability $|S| e^{-2N\delta^2}$ — Hoeffding's inequality for the $N$ conditionally independent indicators that make up the next configuration, applied coordinatewise and union-bounded over the $|S|$ coordinates. And a deviation incurred at step $j$ is then transported forward by the remaining $t - j$ applications of the mean-field map, which is Lipschitz with some constant $K$ uniformly in the activation fraction; the geometric sum $1 + K + \cdots + K^t$ is the accumulated amplification.
--
--   Taken alone this bound degrades with the horizon whenever $K > 1$. What rescues it is the local stability of Lemma 11: near the mean-field fixed point the dynamics contract, so the amplification stops compounding and the horizon can be chosen uniformly. The two lemmas are used together, never separately.
--
--   The formalized bound weakens the source's constants: the exponent is $N\delta^2/2$ rather than $2N\delta^2$ (the per-step tail is proved by a sub-Gaussian chord bound — convexity of the exponential plus $\cosh \lambda \le e^{\lambda^2/2}$ — rather than Hoeffding's lemma), and the prefactor is $2|S|$ per step because the sup-norm event union-bounds over two tails for each coordinate. The functional form, and with it the $1/\sqrt{N}$ rate of Theorem 7, is unchanged.
-- source:
--   Nicolas Gast, Bruno Gaujal and Chen Yan, 'Exponential asymptotic optimality of Whittle index policy' (2023), Lemma C.4; cited as Lemma 10 in Chen and Peng, arXiv:2506.02385v3, Appendix I, p. 43

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Lemma 10 (Multi-step Concentration; Lemma C.4 of Gast, Gaujal and Yan 2023).  There is a
constant `K`, independent of `N`, such that for every horizon `t` and every `δ > 0` the
configuration after `t` steps stays within `(1 + K + ⋯ + Kᵗ) δ` of the `t`-th iterate of the
explicit mean-field map, except on an event of probability at most `2 t |S| e^{−Nδ²/2}`.
The exponent constant is weakened from the source's `2Nδ²` to `Nδ²/2` (a sub-Gaussian
chord bound in place of Hoeffding's lemma) and the prefactor doubled (two tails per
coordinate); neither affects the `1/√N` rate downstream.

The iterate must be that of the **explicit** map at the system's exact activation fraction
`⌊αN⌋ / N`: a map merely characterised on the configurations of the `N`-agent system leaves
the lattice after one step, where the characterisation says nothing.  The error amplifies
geometrically in `t` because each step's deviation is transported by the (Lipschitz) explicit
map, while the per-step failure probability is the Hoeffding bound for `N` conditionally
independent indicators. -/
theorem rmab_multi_step_concentration
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (s0 : Fin N → S) (t : ℕ) (δ : ℝ), 0 < δ →
            ∑ s ∈ Finset.univ.filter (fun s : Fin N → S =>
                (∑ j ∈ Finset.range (t + 1), K ^ j) * δ ≤
                  supNorm (fun x => configuration s x
                    - meanFieldIterate
                        (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)))
                        t (configuration s0) x)),
              rmabLaw P0 P1 π s0 t s
              ≤ 2 * (t : ℝ) * (Fintype.card S : ℝ)
                  * Real.exp (-(N : ℝ) * δ ^ 2 / 2) := by
  sorry

/-! ### M6 — Lemma 11, local stability (Gast, Gaujal and Yan) -/

end MarkovEntanglement
