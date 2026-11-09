-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_lemma_2_4
-- name    : ZamirInversion581.Mult.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:39.883511+00:00
-- url     : https://prove2.me/theorems/b97426f1-d535-4af9-acd2-b72abe5e19e0
-- title:
--   Lemma 2.4 — variance decay of the rank-one walk: $\mathrm{Var}(P^rf)\le q^{-2r}\alpha$
-- statement:
--   Let $F$ be a finite field with $q$ elements, let $n\ge0$, and let $f:F^{n\times n}\to[0,1]$ have mean $\alpha=\mathbb E_X[f(X)]$ under uniform $X$. With $P$ the rank-one walk operator $(Pf)(X)=\mathbb E_{u,v\sim F^n}[f(X+uv^\top)]$, for every integer $r\ge0$,
--
--   $$
--   \mathrm{Var}_X(P^rf)\le q^{-2r}\alpha.
--   $$
--
--   The bound says that a random walk of $r$ rank-one steps makes any $[0,1]$-valued test nearly constant, with an error decaying exponentially in $r$. This is what lets a low-rank perturbation spread a small success probability over almost all inputs.
--
--   Differences from the source: none.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.9, Lemma 2.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_RankOneWalk

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Lemma 2.4, p.9. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "For f : F_q^{n×n} → [0,1], define
(Pf)(X) = E_{u,v∼F_q^n}[f(X + uv⊤)]. If E_X[f(X)] = α, where X is uniform, then for every integer
r ≥ 0, Var(P^r f) ≤ q^{−2r} α." -/
theorem lemma_2_4 (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ)
    (f : Matrix (Fin n) (Fin n) F → ℝ) (hf : ∀ X, 0 ≤ f X ∧ f X ≤ 1)
    (α : ℝ) (hα : unifMean f = α) (r : ℕ) :
    unifVar ((rankOneWalk (F := F) (n := n))^[r] f) ≤
      ((Fintype.card F : ℝ) ^ (2 * r))⁻¹ * α := by sorry

end ZamirInversion581.Mult
