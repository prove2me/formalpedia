-- Prove2me | Theorems.Thm_KServer_ckPotK_nil_coalesced
-- name    : KServer.ckPotK_nil_coalesced
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T10:32:21.4566+00:00
-- url     : https://prove2.me/theorems/c971e8a9-94f4-4946-8a3c-0e47b7ec1cb9
-- title:
--   Initial value of the Coester--Koutsoupias potential at a coalesced start
-- statement:
--   The Coester–Koutsoupias potential at the empty request sequence, for a coalesced initial configuration, equals $\Delta k(k+1)$.
--
--   Let $M$ be a finite metric space, let $\Delta > 0$ bound all distances of $M$, let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$, and start all $k$ servers at a single point $p \in M$. Write $\Phi(\varepsilon)$ for the Coester–Koutsoupias potential (`KServer.ckPotK`) of the instance $(p^k, \varepsilon)$ with the empty request sequence.
--
--   **Statement.**
--   $$\Phi(\varepsilon) \;=\; \Delta\,k\,(k+1).$$
--
--   With no requests, the work function is the matching cost from the initial configuration, so the anchored potential at anchors $x_1,\dots,x_k$ is a sum of distances from $p$; the contributions of each anchor to the $k+1$ terms cancel, leaving the anchor-independent value $2\Delta\bigl(1 + 2 + \dots + k\bigr) = \Delta k (k+1)$. The identity fixes the initial value of the potential, which is what allows the telescoped step inequality to be compared with $(k+1)\,\mathrm{OPT}$ without an additive constant.
--
--   **Formalization Note** The coalesced initial configuration is `fun _ => p`, and the empty request sequence is the empty list; the value is stated as an exact equality, the minimum over anchors being attained at every anchor tuple.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential' (the potential of the initial work function); E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, Section 3.4.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotK_nil_coalesced (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (p : M) :
    ckPotK k M Δ hΔ0 hΔ (fun _ => p) [] = Δ * (k : ℝ) * ((k : ℝ) + 1) := by sorry

end KServer
