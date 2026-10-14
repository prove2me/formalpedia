-- Prove2me | Definitions.Def_KServer_finite_game
-- name    : KServer_finite_game
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-09-06T15:17:19.634888+00:00
-- url     : https://prove2.me/theorems/9def178c-9fd2-439f-8688-db8c0eb50eeb
-- title:
--   Finite k-server minimax game with stopping and an arbitrary prefix payoff
-- statement:
--   Fix a positive number of servers $k$, a metric space $M$, a finite request set $P$, and a real-valued function $b$ on request histories. For a history $l$, current configuration $C$, and remaining horizon $n$, define the finite game value by
--
--   $$V_0(l,C)=-b(l),$$
--
--   and, when $P$ is nonempty,
--
--   $$V_{n+1}(l,C)=\max\left\{-b(l),\ \max_{r\in P}\min_{i\in\{0,\ldots,k-1\}}\left[d(C_i,r)+V_n(lr,C^{i\to r})\right]\right\}.$$
--
--   For $P=\varnothing$, every value is $-b(l)$. Here $lr$ appends the request $r$, and $C^{i\to r}$ moves only server $i$ onto $r$.
--
--   The adversary may stop at any prefix. If it continues, it chooses the request before the algorithm chooses which server to move. All extrema are over finite nonempty sets where they are used. Thus the definition assigns a finite real value even when the ambient metric space is infinite or unbounded.
--
--   The intended payoff is movement cost minus $b$ at the stopping history. Taking $b(\sigma)=k\operatorname{OPT}(C_0,\sigma)$ gives a scalar formulation of the finite-horizon competitive guarantee. The characterization of this value by online algorithms is a separate theorem; the uniform boundedness of the competitive values is still conjectural.
-- source:
--   Original backward-induction formulation for KServer.finite_horizon_uniform_bound (10ab1333-61a5-4d90-ac6b-b692e2316d1e). The game recursion is specified in this definition, and its exact algorithmic interpretation is proved in KServer.finite_game_characterization. Source of the underlying open conjecture: Koutsoupias, The k-server problem (2009), Conjecture 1, preprint p. 2, https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf. This recurrence and characterization are an original formal development, not a claim that the conjecture is proved in that reference.

import Definitions.Def_KServer_model

set_option autoImplicit false

namespace KServer

/-- The exact finite lazy game with stopping payoff `-b l`. The adversary can
stop at any prefix, or request `r ∈ P`; the algorithm then chooses a server.
The argument `n` is the number of requests still available. -/
noncomputable def finiteGameValue {k : ℕ} (hk : 1 ≤ k) {M : Type}
    [MetricSpace M] (P : Finset M) (b : List M → ℝ) :
    ℕ → List M → Config k M → ℝ := by
  classical
  exact fun n => Nat.rec
    (fun l _ => -b l)
    (fun _ V l C => if hP : P.Nonempty then
      max (-b l) (P.sup' hP (fun r =>
        Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i => dist (C i) r + V (l ++ [r]) (Function.update C i r))))
      else -b l) n

end KServer


