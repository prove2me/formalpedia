-- Prove2me | Theorems.Thm_KServer_lazyPot_offset
-- name    : KServer.lazyPot_offset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T15:56:10.612843+00:00
-- url     : https://prove2.me/theorems/4a0e5764-bef8-4685-a078-29e609f917df
-- title:
--   The offset property of the lazy potential
-- statement:
--   This is the **offset property** of the lazy potential $\Psi$ — one of the two conditions a potential must satisfy for the pseudo-cost argument to yield $C$-competitiveness of the Work Function Algorithm. In the formulation of Bein, Chrobak and Larmore the condition reads
--   $$\Psi_{w,r} + (C+1)\min(w) \;\ge\; 0,$$
--   and for $C = 3$ it follows from the sharper inequality proved here: for **every** pair of points $a, b$,
--   $$\Psi_{w,r} \;\ge\; ra + rb + ab \;-\; 4\,w(r,a,b).$$
--
--   Applying this at a configuration $\{r,a,b\}$ on which $w$ is minimised, and discarding the three non-negative distances, gives exactly $\Psi_{w,r} + 4\min(w) \ge 0$.
--
--   ## The proof
--
--   Purely a matter of instantiating the three suprema out of which $\Psi$ is built at well-chosen points, and adding up. Recall
--   $$\Psi_{w,r} = \hat w(r) + \dot w(r), \qquad
--   \dot w(x) = \sup_{p,d,d'}\bigl(\tilde w(x,p) + dd' - w(x,p,d) - w(x,p,d')\bigr).$$
--
--   * In the shadow $\hat w(r) = \sup_A\bigl(\sum_{a' \in A} d(r,a') - w(A)\bigr)$ take $A = \{r,a,b\}$. The term $d(r,r)$ vanishes, leaving $\hat w(r) \ge ra + rb - w(r,a,b)$.
--   * In $\tilde w(r,a) = \sup_{e,e'}\bigl(ae + ae' - w(r,e,e')\bigr)$ take $e = a$, $e' = b$. The term $d(a,a)$ vanishes, leaving $\tilde w(r,a) \ge ab - w(r,a,b)$.
--   * In $\dot w(r)$ take $p = a$ and $d = d' = b$. The term $d(b,b)$ vanishes, leaving $\dot w(r) \ge \tilde w(r,a) - 2\,w(r,a,b) \ge ab - 3\,w(r,a,b)$.
--
--   Adding the first and third bounds gives the statement. Every step is an instance of "the supremum is at least the value at one point", and the three coincidences $d(r,r) = d(a,a) = d(b,b) = 0$ are what make the count come out at exactly four copies of $w(r,a,b)$ — matching $C + 1 = 4$.
--
--   ## Boundedness
--
--   For the instantiations to be legitimate each supremum must be bounded above, and this is where the unit-rate growth of the work function is used, always with the base point $x$ at which the potential is evaluated:
--   $$\hat w(x) \le K_x, \qquad \tilde w(x,y) \le 2\,d(y,x) + K_x, \qquad \dot w(x) \le 3K_x,
--   \qquad K_x := \sum_i d\bigl(x, C_0(i)\bigr).$$
--   The bound on $\dot w$ is the one that has to be checked with care: the term $\tilde w(x,p)$ grows like $2\,d(p,x)$ as $p$ recedes, but the two subtracted work-function values each grow like $d(x,p)$, and the surplus cancels exactly, leaving a bound independent of $p, d, d'$. So the potential is a genuine real number on an arbitrary — in particular unbounded — metric space, with no compactness assumption and with no assumption that any of the suprema is attained.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3, proof of Theorem 1, verification of the offset property (OP) of Lemma 3: 'Psi_{w,r} >= ra + rb - w(r,a,b) + aa + ab - w(r,a,b) + bb - w(r,a,b) - w(r,a,b) = ra + rb + ab - 4 w(r,a,b)'.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lazyPot_offset (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r a b : M) :
    dist r a + dist r b + dist a b - 4 * workFnU C₀ σ ![r, a, b] ≤ lazyPot C₀ σ r := by sorry

end KServer
